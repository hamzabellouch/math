import OAI.Probability.FreeIsing.Ising.OrientedPath

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingOrientedPath
open ConnectedHull TreeKoopman IsingCopySpectral IsingCopyStationarity
open IsingObservationInnovation IsingObservationFactor IsingCopyPathBounds
open IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem edge_reverse_inverse (v : TreeVertex d) (i : ℕ) (hi : i < v.1.length) :
    ((wordAut v.1).toEquiv.symm (edge false v i).1,
      (wordAut v.1).toEquiv.symm (edge false v i).2) =
      edge true (reverseVertex v) (v.1.length - 1 - i) := by
  change ((wordAut v.1).toEquiv.symm (takeVertex v (i + 1)),
    (wordAut v.1).toEquiv.symm (takeVertex v i)) =
    (takeVertex (reverseVertex v) (v.1.length - 1 - i),
      takeVertex (reverseVertex v) (v.1.length - 1 - i + 1))
  rw [← wordAut_reverse_apply_eq_symm, ← wordAut_reverse_apply_eq_symm,
    wordAut_reverse_apply_prefix, wordAut_reverse_apply_prefix]
  have hleft : v.1.length - (i + 1) = v.1.length - 1 - i := by omega
  have hright : v.1.length - i = v.1.length - 1 - i + 1 := by omega
  rw [hleft, hright]

theorem edge_reverse_inverse_oriented (inward : Bool)
    (v : TreeVertex d) (i : ℕ) (hi : i < v.1.length) :
    ((wordAut v.1).toEquiv.symm (edge inward v i).1,
      (wordAut v.1).toEquiv.symm (edge inward v i).2) =
      edge (!inward) (reverseVertex v) (v.1.length - 1 - i) := by
  cases inward
  · exact edge_reverse_inverse v i hi
  · exact congrArg Prod.swap (edge_reverse_inverse v i hi)

omit [IsProbabilityMeasure μ] in
theorem attenuation_reverse_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    (fun x => attenuation hb t inward v (relabel (wordAut v.1) x)) =ᵐ[observationLaw μ]
      attenuation hb t (!inward) (reverseVertex v) := by
  have hnat := ae_all_iff.mpr (fun i : ℕ => cavityObservable_relabel_ae
    hμ hb (wordAut v.1) t (edge inward v i).1 (edge inward v i).2)
  filter_upwards [hnat] with x hx
  unfold attenuation
  have hlen : (reverseVertex v).1.length = v.1.length := List.length_reverse
  rw [hlen]
  apply Finset.prod_bij (fun i _ => v.1.length - 1 - i)
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨v.1.length - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    have he := edge_reverse_inverse_oriented inward v i (Finset.mem_range.mp hi)
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only [Prod.fst, Prod.snd] at hl hr
    rw [hx i, hl, hr]

theorem attenuation_copies_reverse_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    ∀ᵐ q ∂copies beta μ,
      attenuation hb t inward v (copyRelabel (wordAut v.1) q).2.1 =
        attenuation hb t (!inward) (reverseVertex v) q.2.1 ∧
      attenuation hb t inward v (copyRelabel (wordAut v.1) q).2.2 =
        attenuation hb t (!inward) (reverseVertex v) q.2.2 := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae (attenuation_reverse_relabel_ae hμ hb t inward v),
    hr.quasiMeasurePreserving.ae (attenuation_reverse_relabel_ae hμ hb t inward v)] with q hq hq'
  exact ⟨hq, hq'⟩

theorem logSum_suffix_reverse_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (p : ℕ) (hp : p ≤ v.1.length) :
    (fun q => logSum hb t inward v (Finset.Ico p v.1.length)
      (copyRelabel (wordAut v.1) q)) =ᵐ[copies beta μ]
      logSum hb t (!inward) (reverseVertex v) (Finset.range (v.1.length - p)) := by
  have hnat := ae_all_iff.mpr (fun i : ℕ => edgeLogDifference_relabel_ae
    hμ hb (wordAut v.1) t (edge inward v i).1 (edge inward v i).2)
  filter_upwards [hnat] with q hq
  unfold logSum pathLogDifference
  apply Finset.sum_bij (fun i _ => v.1.length - 1 - i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    apply Finset.mem_range.mpr
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨v.1.length - 1 - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro i hi
    have he := edge_reverse_inverse_oriented inward v i (Finset.mem_Ico.mp hi).2
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only [Prod.fst, Prod.snd] at hl hr
    rw [hq i, hl, hr]

theorem attenuation_observationCopy_reverse_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (left : Bool) :
    (fun q => attenuation hb t inward v
      (observationCopy left (copyRelabel (wordAut v.1) q))) =ᵐ[copies beta μ]
      (fun q => attenuation hb t (!inward) (reverseVertex v) (observationCopy left q)) := by
  filter_upwards [attenuation_copies_reverse_ae hμ hb t inward v] with q hq
  cases left
  · exact hq.2
  · exact hq.1

theorem integral_suffix_sq_mul_attenuation_reverse
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (p : ℕ) (hp : p ≤ v.1.length)
    (left : Bool) (k : ℕ) :
    (∫ q, logSum hb t inward v (Finset.Ico p v.1.length) q ^ 2 *
      attenuation hb t inward v (observationCopy left q) ^ k ∂copies beta μ) =
      ∫ q, logSum hb t (!inward) (reverseVertex v) (Finset.range (v.1.length - p)) q ^ 2 *
        attenuation hb t (!inward) (reverseVertex v) (observationCopy left q) ^ k
          ∂copies beta μ := by
  have hf := ((measurable_pathLogDifference hb t (Finset.Ico p v.1.length)
    (edge inward v)).pow_const 2).mul
      (((measurable_attenuation hb t inward v).comp
        (measurable_observationCopy left)).pow_const k)
  calc
    _ = ∫ q, logSum hb t inward v (Finset.Ico p v.1.length)
        (copyRelabel (wordAut v.1) q) ^ 2 * attenuation hb t inward v
        (observationCopy left (copyRelabel (wordAut v.1) q)) ^ k ∂copies beta μ :=
      ((measurePreserving_copies_relabel hμ (wordAut v.1)).hasLaw.integral_comp
        hf.aestronglyMeasurable).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [logSum_suffix_reverse_ae hμ hb t inward v p hp,
        attenuation_observationCopy_reverse_ae hμ hb t inward v left] with q hlog hatt
      rw [hlog, hatt]

end Problem367.IsingOrientedPath

end

end OAI
