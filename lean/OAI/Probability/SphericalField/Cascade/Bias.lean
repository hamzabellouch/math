import Mathlib
import OAI.Probability.SphericalField.Cascade.TotalLaw
import OAI.Probability.SphericalField.Cascade.Blocks

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
def cascadeBiasedLaw (n : ℕ) (z : Fin n → ℝ) (a : ℝ) : Measure (StableCascade n) :=
  normalizedMeasure ((cascadeLaw n z : Measure (StableCascade n)).withDensity
    (fun η => ENNReal.ofReal (cascadeTotal n η^a)))

lemma cascadeLogTotalMoment_integrable (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i) :
    Integrable (fun η => Real.exp (a*Real.log (cascadeTotal n η)))
      (cascadeLaw n z : Measure (StableCascade n)) := by
  obtain ⟨hp,hi⟩ := cascadeTotal_regular n z hz hz0 hz1
  apply (hi a ha).congr
  filter_upwards [hp] with η hη
  rw [Real.rpow_def_of_pos hη,mul_comm]

lemma cascadeBiasedLaw_eq_exponentialTilt (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) :
    cascadeBiasedLaw n z a = exponentialMarkTilt (cascadeLaw n z) a
      (fun C => Real.log (cascadeTotal n C)) := by
  unfold cascadeBiasedLaw exponentialMarkTilt
  congr 1
  apply withDensity_congr_ae
  filter_upwards [(cascadeTotal_regular n z hz hz0 hz1).1] with C hC
  rw [Real.rpow_def_of_pos hC,mul_comm]

lemma cascadeBiasedLaw_probability (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : ∀ i, a < z i) :
    IsProbabilityMeasure (cascadeBiasedLaw n z a) := by
  rw [cascadeBiasedLaw_eq_exponentialTilt n z hz hz0 hz1 a]
  exact exponentialMarkTilt_probability _ (cascadeLogTotalMoment_integrable n z hz hz0 hz1 a ha)

lemma cascadeBiasedLaw_succ_eq_weighted {n : ℕ} (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) :
    cascadeBiasedLaw (n+1) z a = weightedTotalBiasedLaw
      (cascadeLaw n (fun i => z i.succ)) a (z 0) (fun C => Real.log (cascadeTotal n C)) := by
  have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
  have hp := (cascadeTotal_regular n (fun i => z i.succ) htail
    (fun i => hz0 i.succ) (fun i => hz1 i.succ)).1
  unfold cascadeBiasedLaw weightedTotalBiasedLaw
  congr 1
  apply withDensity_congr_ae
  filter_upwards [cascadeTotal_succ_eq z hp] with C hC
  rw [hC]

lemma cascadeRootBlock_factor {n : ℕ} (z : Fin (n+1) → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) {a : ℝ} (ha : a < z 0)
    (ns : List (ℕ × (StableCascade n → ℝ≥0∞))) (hne : ns ≠ [])
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2) :
    (∫⁻ η, markedBlockProbability ns
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)
      ∂cascadeBiasedLaw (n+1) z a) =
      (ns.map (fun nf => ∫⁻ C, nf.2 C ∂cascadeBiasedLaw n (fun i => z i.succ) (z 0))).prod *
      (∫⁻ η, stableBlockProbability (ns.map Prod.fst) η (Fin.elim0 : Fin 0 → ℝ)
        ∂stableTotalBiasedLaw a (z 0)) := by
  have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
  have hM := cascadeLogTotalMoment_integrable n (fun i => z i.succ) htail
    (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp))
  have he := weightedRootBlock_factor _ (hz0 0) (hz1 0) ha (cascadeTotal_measurable n).log hM ns hne hn hm (z := (Fin.elim0 : Fin 0 → ℝ))
  rw [← cascadeBiasedLaw_eq_exponentialTilt n (fun i => z i.succ) htail
      (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0)] at he
  rw [cascadeBiasedLaw_succ_eq_weighted z hz hz0 hz1 a]
  exact he

@[reducible] def CascadeVisitShape : ℕ → Type
  | 0 => ℕ
  | n+1 => List (CascadeVisitShape n)

end SphericalPerceptron
end
end
end

end OAI
