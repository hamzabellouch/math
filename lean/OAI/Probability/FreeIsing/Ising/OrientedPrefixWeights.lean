import OAI.Probability.FreeIsing.Ising.CopyPathVariance
import OAI.Probability.FreeIsing.Ising.OrientedPathWeights

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut TreeOrbitAverage ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem takeVertex_takeVertex_of_le (v : TreeVertex d) {i p : ℕ} (hi : i ≤ p) :
    takeVertex (takeVertex v p) i = takeVertex v i := by
  apply Subtype.ext
  simp [takeVertex, List.take_take, Nat.min_eq_left hi]

theorem edge_takeVertex (inward : Bool) (v : TreeVertex d) {i p : ℕ} (hi : i < p) :
    edge inward (takeVertex v p) i = edge inward v i := by
  cases inward <;> simp only [edge, Bool.false_eq_true, ↓reduceIte]
  all_goals rw [takeVertex_takeVertex_of_le v (by omega),
    takeVertex_takeVertex_of_le v (by omega)]

theorem logSum_prefix (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) (p : ℕ) :
    logSum hb t inward (takeVertex v p) (Finset.range p) =
      logSum hb t inward v (Finset.range p) := by
  funext q
  unfold logSum pathLogDifference
  apply Finset.sum_congr rfl
  intro i hi
  rw [edge_takeVertex inward v (Finset.mem_range.mp hi)]

def extensionAt (v : TreeVertex d) (p : ℕ) :
    Extension (v.1.take p) (v.1.length - p) :=
  ⟨v.1.drop p, List.length_drop, by rw [List.take_append_drop]; exact v.2⟩

@[simp] theorem endpoint_extensionAt (v : TreeVertex d) (p : ℕ) :
    endpoint (extensionAt v p) = v := by
  apply Subtype.ext
  exact List.take_append_drop p v.1

theorem prefix_edges_in_stem (inward : Bool) (v : TreeVertex d) {p : ℕ}
    (hp : p ≤ v.1.length) :
    ∀ i ∈ Finset.range p, (edge inward v i).1.1.length ≤ (v.1.take p).length ∧
      (edge inward v i).2.1.length ≤ (v.1.take p).length := by
  intro i hi
  have hi' := Finset.mem_range.mp hi
  cases inward <;> simp only [edge, Bool.false_eq_true, ↓reduceIte,
    takeVertex, List.length_take, Nat.min_eq_left hp]
  all_goals constructor <;> omega

theorem exists_logSum_prefix_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (inward : Bool) (v : TreeVertex d) (p : ℕ), p ≤ v.1.length →
      (∫ q, logSum hb t inward v (Finset.range p) q ^ 2 ∂copies beta μ) ≤
        C * (p : ℝ) * ∫ q, cavityLogDifference hb t u w q ^ 2 ∂copies beta μ := by
  obtain ⟨C, hC, h⟩ := exists_cavityLog_path_variance_bound hμ hd hb hthreshold
  refine ⟨C, hC, ?_⟩
  intro t u w huw inward v p hp
  have hv := h t u w huw (TreeAut.refl d) (takeVertex v p)
  have hlen : (takeVertex v p).1.length = p := by
    exact List.length_take_of_le hp
  simp only [TreeAut.refl, Equiv.refl_apply] at hv
  have hf (q : IsingConditionalCopyBounds.CopySpace d) :
      (∑ i : Fin (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) i) (takeVertex (takeVertex v p) (i + 1)) q) =
      ∑ i ∈ Finset.range (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) i) (takeVertex (takeVertex v p) (i + 1)) q :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => cavityLogDifference hb t
      (takeVertex (takeVertex v p) i) (takeVertex (takeVertex v p) (i + 1)) q) _
  have hr (q : IsingConditionalCopyBounds.CopySpace d) :
      (∑ i : Fin (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) (i + 1)) (takeVertex (takeVertex v p) i) q) =
      ∑ i ∈ Finset.range (takeVertex v p).1.length, cavityLogDifference hb t
        (takeVertex (takeVertex v p) (i + 1)) (takeVertex (takeVertex v p) i) q :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => cavityLogDifference hb t
      (takeVertex (takeVertex v p) (i + 1)) (takeVertex (takeVertex v p) i) q) _
  simp_rw [hf, hr] at hv
  rw [← logSum_prefix hb t inward v p]
  cases inward
  · simpa only [logSum, pathLogDifference, edge, Bool.false_eq_true, ↓reduceIte,
      edgeLogDifference_eq_cavityLogDifference, Fin.sum_univ_eq_sum_range,
      hlen, TreeAut.refl, Equiv.refl_apply] using hv.2
  · simpa only [logSum, pathLogDifference, edge, ↓reduceIte,
      edgeLogDifference_eq_cavityLogDifference, Fin.sum_univ_eq_sum_range,
      hlen, TreeAut.refl, Equiv.refl_apply] using hv.1

theorem integral_prefix_weight_mul_le_of_tail
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (left inward : Bool) (v : TreeVertex d)
    {p : ℕ} (hp : p ≤ v.1.length) {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (htail : observationLaw μ
      {x | a < extensionAverage hb t inward (v.1.take p) (v.1.length - p) x} ≤
        ENNReal.ofReal ε) :
    (∫ q, logSum hb t inward v (Finset.range p) q ^ 2 *
      attenuation hb t inward v (observationCopy left q) ^ 2 ∂copies beta μ) ≤
      a * (∫ q, logSum hb t inward v (Finset.range p) q ^ 2 ∂copies beta μ) +
        ((p : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) * ε := by
  simpa only [logSum, endpoint_extensionAt, Finset.card_range] using
    integral_log_weight_mul_le_of_tail hμ hb ht (Finset.range p) (edge inward v)
      left inward (prefix_edges_in_stem inward v hp) (extensionAt v p) ha hε htail

end Problem367.IsingOrientedPath

end

end OAI
