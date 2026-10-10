import OAI.NumberTheory.DirichletL.Detector.LowRowMellin

namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowRowMellinIntegrand_common_support (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset PhysicalRowIndex,∀v : ℝ,∀r∉R,
      lowRowMellinIntegrand C W0 W1 Ω X Y r v=0 := by
  have hs := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  have hm := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hs.toFinset×ˢhm.toFinset,?_⟩
  intro v r hr
  simp only [Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support] at hr
  by_cases h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0
  · unfold lowRowMellinIntegrand
    rw [lowAdditiveCoefficient_outer_zero C W1 Y r.1 r.2 v h,mul_zero]
  · have ho : Ω (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      by_contra ho
      exact hr ⟨h,ho⟩
    simp [lowRowMellinIntegrand,ho]

lemma lowRowMellinIntegrand_mul_summable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (v : ℝ) (B : PhysicalRowIndex→ℂ) :
    Summable (fun r=>lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  apply summable_of_ne_finset_zero (s:=R)
  intro r hr
  rw [hR v r hr,zero_mul]

lemma lowRowMellinIntegrand_sum_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    Integrable (fun v : ℝ=>∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  simp_rw [he]
  exact integrable_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)

lemma lowRowMellinIntegrand_tsum_integral (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,∫v : ℝ,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∫v : ℝ,∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  rw [tsum_eq_sum (s:=R) (fun r hr=>by simp only [hR _ r hr,zero_mul,integral_zero])]
  simp_rw [he]
  exact (integral_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)).symm

theorem physicalRowWeight_tsum_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B r)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,∑'r : PhysicalRowIndex,
          lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v*B r := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  simp_rw [physicalRowWeight_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [mul_assoc,←integral_mul_const]
  repeat rw [tsum_mul_left]
  congr 2
  exact lowRowMellinIntegrand_tsum_integral C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩ hΩ0 X Y hX hY B

end SevenEighths.ProbePhysical
end

end OAI
