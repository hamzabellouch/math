import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortResidue
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRadialModel

namespace OAI

/-! The radial model and the short inverse residue differ only by the
proved squarefree lattice error and an absolutely convergent Euler tail. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma UniformLogWeights.radial_main_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i r, primary r → ∀ U, 0 < U →
      ‖metaplecticMain r 0 (W i) U‖ ≤ K*U^(5/6:ℝ)*norm r^(-1/6:ℝ) := by
  obtain ⟨M,hM,hb⟩ := h.mellin_decay 1 0
  refine ⟨|metaplecticA0| * M,by positivity,?_⟩
  intro i r hr U hU
  have hn := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hm : ‖mellin (W i) (5/6)‖ ≤ M := by
    simpa using hb i (5/6) (by norm_num) 0
  have hphi := metaplecticTotient_le_norm hr
  have hphi0 : 0 ≤ metaplecticTotient r := by
    unfold metaplecticTotient
    positivity
  rw [metaplecticMain,ite_eq_left rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hU _),
    abs_of_nonneg hphi0,abs_of_pos (Real.rpow_pos_of_pos hn _)]
  calc
    _ ≤ |metaplecticA0| * U^(5/6:ℝ)*norm r*norm r^(-7/6:ℝ)*M := by gcongr
    _ = _ := by
      have he : norm r*norm r^(-7/6:ℝ) = norm r^(-1/6:ℝ) := by
        calc
          _ = norm r^(1:ℝ)*norm r^(-7/6:ℝ) := by rw [Real.rpow_one]
          _ = norm r^((1:ℝ)+(-7/6)) := (Real.rpow_add hn _ _).symm
          _ = _ := by norm_num
      calc
        _ = (|metaplecticA0| * M)*U^(5/6:ℝ)*(norm r*norm r^(-7/6:ℝ)) := by ring
        _ = _ := by rw [he]

theorem UniformLogWeights.radial_short_model_error
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K E : ℝ, 0 ≤ K ∧ 0 ≤ E ∧ ∀ i r, primary r → Squarefree r →
      ∀ U C, 0 < U → 0 < C →
      C ≤ Real.sqrt (Real.exp (h.realPower (-1/6)).radius*U) →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C‖ ≤
        K*norm r^(δ-1/6)*U^(1/3:ℝ)+
          E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)*C^(-(99/100):ℝ) := by
  obtain ⟨K,hK,hmodel⟩ := h.radial_model_finite_error hδ
  obtain ⟨M,hM,hmain⟩ := h.radial_main_bound
  obtain ⟨D,hD,htail⟩ := metaplecticRadialEulerPartial_tail
  refine ⟨K,M*D,hK.le,mul_nonneg hM hD,?_⟩
  intro i r hr hsr U C hU hC hCD
  let V := Real.sqrt (Real.exp (h.realPower (-1/6)).radius*U)
  calc
    _ ≤ ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r V‖+
      ‖metaplecticMain r 0 (W i) U*
        (metaplecticRadialEulerPartial r V-metaplecticRadialEulerPartial r C)‖ := by
      have he : angularSmoothModel r 0 (W i) U-
          metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C =
        (angularSmoothModel r 0 (W i) U-
          metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r V)+
        metaplecticMain r 0 (W i) U*
          (metaplecticRadialEulerPartial r V-metaplecticRadialEulerPartial r C) := by ring
      rw [he]
      exact norm_add_le _ _
    _ ≤ K*norm r^(δ-1/6)*U^(1/3:ℝ)+
        (M*U^(5/6:ℝ)*norm r^(-1/6:ℝ))*(D*C^(-(99/100):ℝ)) := by
      apply add_le_add (hmodel i r hr hsr U hU)
      rw [norm_mul]
      exact mul_le_mul (hmain i r hr U hU) (htail r C V hC hCD)
        (_root_.norm_nonneg _)
        (mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hU.le _))
          (Real.rpow_nonneg (norm_nonneg r) _))
    _ = _ := by ring

theorem LogarithmicWeightFamily.radial_short_model_error
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) :
    ∃ B K E : ℝ, 1 ≤ B ∧ 0 ≤ K ∧ 0 ≤ E ∧ ∀ i r,
      primary r → Squarefree r → ∀ U C, 0 < U → 0 < C →
      C ≤ Real.sqrt (B*U) →
      ‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C‖ ≤
        K*(Y i)^s*norm r^(δ-1/6)*U^(1/3:ℝ)+
          E*(Y i)^s*U^(5/6:ℝ)*norm r^(-1/6:ℝ)*C^(-(99/100):ℝ) := by
  let h₀ := h.normalize hs
  let B := Real.exp (h₀.realPower (-1/6)).radius
  obtain ⟨K,E,hK,hE,hbound⟩ := h₀.radial_short_model_error hδ
  refine ⟨B,K,E,Real.one_le_exp (h₀.realPower (-1/6)).radius_nonneg,hK,hE,?_⟩
  intro i r hr hsr U C hU hC hCD
  have hY : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
  have hb := hbound i r hr hsr U C hU hC hCD
  have he : angularSmoothModel r 0 (normalizedLogWeight Y W s i) U-
      metaplecticMain r 0 (normalizedLogWeight Y W s i) U*metaplecticRadialEulerPartial r C =
      (((Y i)^(-s):ℝ):ℂ)*(angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C) := by
    unfold normalizedLogWeight
    simp_rw [Complex.real_smul]
    rw [angularSmoothModel_const_mul,metaplecticMain_const_mul]
    ring
  change ‖angularSmoothModel r 0 (normalizedLogWeight Y W s i) U-
    metaplecticMain r 0 (normalizedLogWeight Y W s i) U*metaplecticRadialEulerPartial r C‖ ≤ _ at hb
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^s*(Y i)^(-s) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^s*((Y i)^(-s)*‖angularSmoothModel r 0 (W i) U-
        metaplecticMain r 0 (W i) U*metaplecticRadialEulerPartial r C‖) := by
          rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^s*(K*norm r^(δ-1/6)*U^(1/3:ℝ)+
        E*U^(5/6:ℝ)*norm r^(-1/6:ℝ)*C^(-(99/100):ℝ)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
