import OAI.Probability.InvariantIsing.Cavity.ConsecutiveFieldPressure

namespace OAI

/-! The field contribution on a prescribed group slice is deterministic. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma restrictedRotatedPressure_group_field {N : ℕ} (hN : 0<N)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (count : A → ℕ)
    (hc : ∀ a, count a ≤ spinGroupSize group a)
    (γ mag b : A → ℝ)
    (hg : ∀ a, (spinGroupSize group a : ℝ)=N*γ a)
    (hm : ∀ a, (count a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (eig : Fin N → ℝ) (U : Rotation N) :
    restrictedRotatedPressure (spinGroupSlice group count) eig U (fun i => b (group i)) =
      restrictedRotatedPressure (spinGroupSlice group count) eig U (fun _ => 0)+
        ∑ a, γ a*b a*mag a := by
  have hS := spinGroupSlice_nonempty group count hc
  have hM := spinGroupFieldConstant_magnetization group count b γ mag hg hm
  have hlog : restrictedSpinLog (spinGroupSlice group count)
      (fun σ => rotatedEnergy eig U σ+fieldEnergy (fun i => b (group i)) σ) =
      restrictedSpinLog (spinGroupSlice group count) (fun σ => rotatedEnergy eig U σ)+
        N*(∑ a, γ a*b a*mag a) := by
    rw [← restrictedSpinLog_add_const _ hS]
    unfold restrictedSpinLog
    congr 2
    apply Finset.sum_congr rfl
    intro σ hσ
    dsimp only
    rw [fieldEnergy_on_group_slice group count b hσ, hM]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold restrictedRotatedPressure
  rw [hlog]
  simp only [fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]
  field_simp

lemma mean_restrictedRotatedPressure_group_field {N : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : Fin N → A) (count : A → ℕ)
    (hc : ∀ a, count a ≤ spinGroupSize group a)
    (γ mag b : A → ℝ)
    (hg : ∀ a, (spinGroupSize group a : ℝ)=N*γ a)
    (hm : ∀ a, (count a : ℝ)=spinGroupSize group a*((1+mag a)/2))
    (eig : Fin N → ℝ)
    (hi : Integrable (fun U : SpecialOrthogonal N =>
      restrictedRotatedPressure (spinGroupSlice group count) eig (specialRotation U) (fun _ => 0)) μ) :
    (∫ U, restrictedRotatedPressure (spinGroupSlice group count) eig
      (specialRotation U) (fun i => b (group i)) ∂μ) =
      (∫ U, restrictedRotatedPressure (spinGroupSlice group count) eig
        (specialRotation U) (fun _ => 0) ∂μ)+(∑ a, γ a*b a*mag a) := by
  simp_rw [restrictedRotatedPressure_group_field hN group count hc γ mag b hg hm]
  rw [integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul]

end InvariantIsing

end

end OAI
