import Mathlib
import OAI.Probability.SphericalField.Cascade.Bias

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable
def cascadeVisitCount : (n : ℕ) → CascadeVisitShape n → ℕ
  | 0, r => r
  | n+1, ss => (ss.map (cascadeVisitCount n)).sum

def CascadeVisitShape.Valid : (n : ℕ) → CascadeVisitShape n → Prop
  | 0, r => 1 ≤ r
  | n+1, ss => ss ≠ [] ∧ ∀ s ∈ ss, CascadeVisitShape.Valid n s

lemma cascadeVisitCount_pos (n : ℕ) (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    1 ≤ cascadeVisitCount n s := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    obtain ⟨hne,hs⟩ := hs
    change (s.map (cascadeVisitCount n)).sum ≥ 1
    cases s with
    | nil => exact (hne rfl).elim
    | cons h t =>
      simp only [List.map_cons,List.sum_cons]
      have := ih h (hs h (by simp))
      omega

def cascadeShapeProbability : (n : ℕ) → (Fin n → ℝ) → CascadeVisitShape n → StableCascade n → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, z, ss, η => markedBlockProbability
      (ss.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)))
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)

lemma cascadeShapeProbability_measurable (n : ℕ) (z : Fin n → ℝ) (s : CascadeVisitShape n) :
    Measurable (cascadeShapeProbability n z s) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : ∀ nf ∈ s.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)),
        Measurable nf.2 := by
      intro nf hnf
      obtain ⟨s',_,rfl⟩ := List.mem_map.mp hnf
      exact ih (fun i => z i.succ) s'
    have hF := logMarkShift_measurable (centeredLogMark_measurable
      (cascadeLaw n (fun i => z i.succ)) (z 0) (cascadeTotal_measurable n).log)
    exact (markedBlockProbability_measurable _ hm 0).comp
      ((Measure.measurable_map _ hF).prodMk measurable_const)

def cascadeShapeLikelihood : (n : ℕ) → (Fin n → ℝ) → ℝ → CascadeVisitShape n → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, z, a, ss =>
      (ss.map (cascadeShapeLikelihood n (fun i => z i.succ) (z 0))).prod *
      ENNReal.ofReal (stableEppfValue a (z 0) (ss.map (fun s => (cascadeVisitCount n s : ℝ))))

theorem cascadeShapeProbability_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i)
    (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    (∫⁻ η, cascadeShapeProbability n z s η ∂cascadeBiasedLaw n z a) =
      cascadeShapeLikelihood n z a s := by
  induction n generalizing a with
  | zero =>
    have := cascadeBiasedLaw_probability 0 z hz hz0 hz1 a ha
    simp only [cascadeShapeProbability,cascadeShapeLikelihood,lintegral_const,measure_univ,mul_one]
  | succ n ih =>
    obtain ⟨hne,hs⟩ := hs
    let ns := s.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s))
    have hns : ns ≠ [] := by
      intro he
      apply hne
      exact List.map_eq_nil_iff.mp he
    have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
      intro nf hnf; obtain ⟨s',hmem,rfl⟩ := List.mem_map.mp hnf
      exact cascadeVisitCount_pos n s' (hs s' hmem)
    have hm : ∀ nf ∈ ns, Measurable nf.2 := by
      intro nf hnf; obtain ⟨s',_,rfl⟩ := List.mem_map.mp hnf
      exact cascadeShapeProbability_measurable n (fun i => z i.succ) s'
    change (∫⁻ η, markedBlockProbability ns _ _ ∂cascadeBiasedLaw (n+1) z a) = _
    rw [cascadeRootBlock_factor z hz hz0 hz1 (ha 0) ns hns hn hm,
      stableBlockProbability_eppf (hz0 0) (hz1 0) (ha 0) (ns.map Prod.fst)
        (fun emptyMap => hns (List.map_eq_nil_iff.mp emptyMap))
        (by intro r hr; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr; exact hn nf hmem)]
    simp only [ns,List.map_map,Function.comp_def,cascadeShapeLikelihood,stableEppfValue,List.length_map]
    congr 2
    apply List.map_congr_left
    intro s' hmem
    exact ih (fun i => z i.succ) (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h))
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp)) s' (hs s' hmem)

end SphericalPerceptron

namespace SphericalPerceptron

lemma cascadeBiasedLaw_zero (n : ℕ) (z : Fin n → ℝ) :
    cascadeBiasedLaw n z 0 = (cascadeLaw n z : Measure (StableCascade n)) := by
  simp [cascadeBiasedLaw,normalizedMeasure]

lemma stableBlockProbability_eppf_value {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List ℕ) (hne : ns ≠ []) (hn : ∀ n ∈ ns, 1 ≤ n) :
    (∫⁻ η, stableBlockProbability ns η (Fin.elim0 : Fin 0 → ℝ) ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (stableEppfValue a b (ns.map (fun n : ℕ => (n:ℝ)))) := by
  simpa only [stableEppfValue,List.length_map,List.map_map,Function.comp_def] using
    stableBlockProbability_eppf hb hb1 ha ns hne hn (Fin.elim0 : Fin 0 → ℝ)

lemma cascadeShapeProbability_law (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    (∫⁻ η, cascadeShapeProbability n z s η ∂(cascadeLaw n z : Measure (StableCascade n))) =
      cascadeShapeLikelihood n z 0 s := by
  rw [← cascadeBiasedLaw_zero n z]
  exact cascadeShapeProbability_integral n z hz hz0 hz1 0 hz0 s hs

end SphericalPerceptron
end
end
end

end OAI
