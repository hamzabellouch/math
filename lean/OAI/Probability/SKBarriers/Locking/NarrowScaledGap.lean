import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowContinuumTrial
import OAI.Probability.SKBarriers.Locking.NarrowNegativeCoefficient
import OAI.Probability.SKBarriers.Locking.NarrowScaledRemainder
import OAI.Probability.SKBarriers.Locking.TripleNegativeCoefficient

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem narrowConstrainedPressure_scaled_gap {β m : ℝ} (hβ : β≠0) (hm : 0 < m) :
    ∃ ρ₀ c : ℝ, 0<ρ₀ ∧ 0<c ∧ ∀ (α : StieltjesFunction ℝ),
      (∀ z,α z∈Icc (0:ℝ) 1) → α 1=1 → ∀ (N : ℕ), 0<N →
      ∀ ρ r q u δ : ℝ, 0<ρ → ρ≤ρ₀ → ρ^8≤r → r+ρ≤q → q≤1 → r<u → u≤1 →
      (∀ s∈Icc r u,scalarCDFOverlap β α s=s) → m≤α r →
      scalarCDFSusceptibilityAverage β α q=(∫ x in q..1,α x)+α q*(q-scalarCDFOverlap β α q) →
      |q-scalarCDFOverlap β α q|≤ρ^13 → α (r+ρ^8)-α (r-ρ^8)≤ρ^4 →
      |δ|≤2*ρ^20 → Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
      matrixConstrainedPressure N 3 β (tripleGram r δ q)≤3*scalarCDFParisi β α-c*ρ^3*δ^2 := by
  let D := narrowExpansionDenominator β
  let E := narrowExpansionErrorConstant β
  let C := narrowCDFErrorConstant β
  let c := β^2*m*scalarJointLossConstant β m
  let A := 3*β^2+2*C+2*E+36*β^2
  have hD1 : 1≤D := narrowExpansionDenominator_ge_one β
  have hD : 0<D := lt_of_lt_of_le zero_lt_one hD1
  have hE : 0<E := narrowExpansionErrorConstant_pos β
  have hC : 0≤C := narrowCDFErrorConstant_nonneg β
  have hc : 0<c := mul_pos (mul_pos (sq_pos_of_ne_zero hβ) hm) (scalarJointLossConstant_pos hβ hm)
  have hA : 0<A := by dsimp only [A]; positivity
  let f := fun x : ℝ => x^2+16*D*x^32+2*x^20+A*x
  obtain ⟨ρ₀,hρ₀,hf⟩ := continuousAt_small_interval
    (show ContinuousAt f 0 by dsimp only [f]; fun_prop)
    (b:=min (1/2) (c/2)) (by simpa only [f,zero_pow (by decide : 2≠0),zero_pow (by decide : 32≠0),zero_pow (by decide : 20≠0),mul_zero,add_zero] using lt_min (by norm_num : (0:ℝ)<1/2) (half_pos hc)) zero_lt_one
  refine ⟨ρ₀,c/2,hρ₀.1,half_pos hc,?_⟩
  intro α hα hα1 N hN ρ r q u δ hρ hρle hhr hrq hq hru hu hΓ hmr hS hdev hosc hδ hGram
  have hρ1 : ρ≤1 := hρle.trans hρ₀.2.le
  have Hf := hf ρ ⟨hρ.le,hρle⟩
  have Hf1 : f ρ<1/2 := Hf.trans_le (min_le_left _ _)
  have Hfc : f ρ<c/2 := Hf.trans_le (min_le_right _ _)
  have hθ : 0≤ρ^2 := sq_nonneg ρ
  have hθhalf : ρ^2≤1/2 := by dsimp only [f] at Hf1; nlinarith [mul_nonneg (show 0≤16*D by positivity) (pow_nonneg hρ.le 32),pow_nonneg hρ.le 20,mul_nonneg hA.le hρ.le]
  have hsmallδ : 16*D*ρ^32≤1 := by dsimp only [f] at Hf1; nlinarith [pow_nonneg hρ.le 20,mul_nonneg hA.le hρ.le]
  have hδone : |δ|≤1 := by dsimp only [f] at Hf1; nlinarith [mul_nonneg (show 0≤16*D by positivity) (pow_nonneg hρ.le 32),mul_nonneg hA.le hρ.le]
  have hAc : A*ρ≤c/2 := by dsimp only [f] at Hfc; nlinarith [mul_nonneg (show 0≤16*D by positivity) (pow_nonneg hρ.le 32),pow_nonneg hρ.le 20]
  have hh : 0<ρ^8 := pow_pos hρ _
  have hh1 : ρ^8≤1 := pow_le_one₀ hρ.le hρ1
  have hhalf : 1/2≤1-ρ^2 := by linarith
  have ha : 0<1-ρ^2 := by linarith
  have hr : 0≤r := hh.le.trans hhr
  have hhq : r+ρ^8≤q := by
    have H : ρ^8≤ρ := by simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : 1≤8)
    linarith
  have hrq' : r≤q := by linarith
  have hε : 0<ρ^8/D := div_pos hh hD
  have hδ2 : δ^2≤4*ρ^40 := by
    calc
      _ = |δ|^2 := (sq_abs _).symm
      _ ≤ (2*ρ^20)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hδ
      _ = _ := by ring
  have hδsmall : 4*δ^2≤ρ^8/D := by
    apply (le_div_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_right hsmallδ hh.le
    have H' := mul_le_mul_of_nonneg_right hδ2 (show 0≤4*D by positivity)
    nlinarith only [H,H']
  have HC := narrowCDFTrialCoefficient_quantitative hβ α hα hα1 hh hr hrq' hq hru hu hΓ hm hmr hhalf hθ
    (by ring : (1-ρ^2)+ρ^2=1) hS hdev
  have Hosc := mul_le_mul_of_nonneg_left hosc hC
  have HD := mul_le_mul_of_nonneg_left (show ρ≤q-r by linarith) (show 0≤c*ρ^2 by positivity)
  have Heq : 3*β^2*ρ^13/ρ^8=3*β^2*ρ^5 := by field_simp
  rw [Heq] at HC
  have HC' : narrowCDFTrialCoefficient β α r (ρ^8) q (1-ρ^2) (ρ^2)≤(3*β^2+2*C)*ρ^4-c*ρ^3 := by
    have Hp := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1 (by decide : 4≤5)) (show 0≤3*β^2 by positivity)
    change _≤_+C*(_+(ρ^2)^2)-c*ρ^2*(q-r) at HC
    nlinarith only [HC,Hosc,HD,Hp]
  have HP := narrowConstrainedPressure_continuum_trial hN β δ α hα hα1 hh hhr hhq hq ha hθ
    (by ring : (1-ρ^2)+ρ^2=1) hGram hε hδsmall hδone (narrowExpansion_smallness β hh hh1 ha.le hθ (by ring))
  have HR := narrow_scaled_remainder β hρ hρ1 hδ
  have Hrem : tripleExpansionConstant (ρ^8/D)*|δ|^3+β^2*δ^4*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2≤
      δ^2*((2*E+36*β^2)*ρ^4) := by
    have H := mul_le_mul_of_nonneg_left HR (sq_nonneg δ)
    have HE : |δ|^3=δ^2*|δ| := by rw [←sq_abs δ]; ring
    rw [HE]
    nlinarith only [H]
  have Hquad := mul_le_mul_of_nonneg_left HC' (sq_nonneg δ)
  have Habs := mul_le_mul_of_nonneg_right hAc (pow_nonneg hρ.le 3)
  have Hfinal := mul_le_mul_of_nonneg_left Habs (sq_nonneg δ)
  dsimp only [A] at Hfinal
  change _≤3*scalarCDFParisi β α+δ^2*(_)+tripleExpansionConstant (ρ^8/D)*|δ|^3+β^2*δ^4*((2*(1-ρ^2)^2+(ρ^2)^2)/ρ^8)^2 at HP
  nlinarith only [HP,Hrem,Hquad,Hfinal]

end SK.Analytic

end
end

end OAI
