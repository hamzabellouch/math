import OAI.NumberTheory.CubicMoment.Transform.MetaplecticSquarefreeRadial
import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeModel
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortLogInverse

namespace OAI

/-! The actual radial model has the same finite residue density as the
short inverse completion, up to the proved squarefree lattice error. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularSmoothModel_const_mul (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (U : ℝ) (z : ℂ) :
    angularSmoothModel r ℓ (fun x => z*W x) U = z*angularSmoothModel r ℓ W U := by
  unfold angularSmoothModel
  rw [←tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : primary u
  · simp only [hu,ite_true]
    ring
  · simp only [hu,ite_false,mul_zero]

lemma radial_squarefree_main_scaled {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) {U : ℝ} (hU : 0 < U) (B : ℝ) :
    ((cStar*(norm r*U)^(-1/6:ℝ):ℝ):ℂ)*
      squarefreeCoprimeRadialMain r (fun x => ((x^(-1/6:ℝ):ℝ):ℂ)*W x) U B =
        metaplecticMain r 0 W U*metaplecticRadialEulerPartial r (Real.sqrt (B*U)) := by
  rw [squarefreeCoprimeRadialMain_eq hr hsr,integral_radial_model_weight]
  have hs := congrArg (fun x : ℝ => (x:ℂ))
    (metaplectic_radial_density_scale (norm_pos_of_ne_zero (primary_ne_zero hr)) hU
      (metaplecticTotient r))
  push_cast at hs
  simp only [metaplecticMain,ite_true]
  push_cast
  calc
    _ = ((cStar*(norm r*U)^(-1/6:ℝ)*(2*Real.pi*U/(9*Real.sqrt 3))*
        (metaplecticTotient r/norm r):ℝ):ℂ)*mellin W (5/6)*
          metaplecticRadialEulerPartial r (Real.sqrt (B*U)) := by push_cast; ring
    _ = _ := by push_cast; rw [hs]

theorem UniformLogWeights.radial_model_finite_error {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 0 < U →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r
          (Real.sqrt (Real.exp (h.realPower (-1/6)).radius*U))‖ ≤
        K*norm r^(δ-1/6)*U^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := (h.realPower (-1/6)).squarefreeCoprimeRadialLattice_centered hδ
  refine ⟨|cStar| * C,by have := cStar_pos; positivity,?_⟩
  intro i r hr hsr U hU
  have hn := norm_pos_of_ne_zero (primary_ne_zero hr)
  rw [angularSmoothModel_eq hsr 0 (W i) hU,
    show theta 0 r = 1 by simp [theta],mul_one,
    ←radial_squarefree_main_scaled hr hsr (W i) hU,
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (mul_pos hn hU) _)]
  calc
    _ ≤ (|cStar| * (norm r*U)^(-1/6:ℝ))*(C*norm r^δ*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left (hbound i r hr hsr U hU) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow hn.le hU.le,Real.sqrt_eq_rpow,
        show δ-1/6 = (-1/6:ℝ)+δ by ring,Real.rpow_add hn,
        show (1/3:ℝ) = (-1/6:ℝ)+1/2 by norm_num,Real.rpow_add hU]
      ring

theorem LogarithmicWeightFamily.radial_model_finite_error
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    ∃ B K : ℝ, 1 ≤ B ∧ 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 0 < U →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r (Real.sqrt (B*U))‖ ≤
        K*(Y i)^s*norm r^(δ-1/6)*U^(1/3:ℝ) := by
  let h₀ := h.normalize hs
  let B := Real.exp (h₀.realPower (-1/6)).radius
  have hB : 1 ≤ B := Real.one_le_exp (h₀.realPower (-1/6)).radius_nonneg
  obtain ⟨K,hK,hbound⟩ := h₀.radial_model_finite_error hδ
  refine ⟨B,K,hB,hK,?_⟩
  intro i r hr hsr U hU
  have hY : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
  have hb := hbound i r hr hsr U hU
  have he : angularSmoothModel r 0 (normalizedLogWeight Y W s i) U-
      metaplecticMain r 0 (normalizedLogWeight Y W s i) U*
        metaplecticRadialEulerPartial r (Real.sqrt (B*U)) =
      (((Y i)^(-s):ℝ):ℂ)*(angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r (Real.sqrt (B*U))) := by
    unfold normalizedLogWeight
    simp_rw [Complex.real_smul]
    rw [angularSmoothModel_const_mul,metaplecticMain_const_mul]
    ring
  change ‖angularSmoothModel r 0 (normalizedLogWeight Y W s i) U-
    metaplecticMain r 0 (normalizedLogWeight Y W s i) U*
      metaplecticRadialEulerPartial r (Real.sqrt (B*U))‖ ≤ _ at hb
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^s*(Y i)^(-s) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^s*((Y i)^(-s)*‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r (Real.sqrt (B*U))‖) := by
          rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^s*(K*norm r^(δ-1/6)*U^(1/3:ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
