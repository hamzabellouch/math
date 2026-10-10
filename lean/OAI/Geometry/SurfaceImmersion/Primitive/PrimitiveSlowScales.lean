import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold

namespace OAI

/-! The finite slow scales in the high-accuracy primitive realization.
These choices precede every accuracy order in its mean iteration. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

def amplitudeExponent (j : ℕ) : ℝ := (1/4)*(6/5 : ℝ)^j
def scaleExponent (σ : ℝ) (steps j : ℕ) : ℝ := (j : ℝ)*σ/(steps : ℝ)

lemma amplitudeExponent_pos (j : ℕ) : 0 < amplitudeExponent j := by
  unfold amplitudeExponent
  positivity

lemma amplitudeExponent_zero : amplitudeExponent 0 = 1/4 := by
  simp [amplitudeExponent]

lemma amplitudeExponent_succ (j : ℕ) :
    amplitudeExponent (j+1) = (6/5)*amplitudeExponent j := by
  simp only [amplitudeExponent,pow_succ]
  ring

lemma amplitudeExponent_lower (j : ℕ) : 1/4 ≤ amplitudeExponent j := by
  induction j with
  | zero => rw [amplitudeExponent_zero]
  | succ j ih => rw [amplitudeExponent_succ]; linarith

/-- A finite number of amplitude improvements achieves any prescribed finite
metric order. No derivative count enters the later accuracy choices. -/
lemma exists_amplitude_steps (R N : ℕ) :
    ∃ steps : ℕ, 1 ≤ steps ∧ (N : ℝ)+R+1 < 2*amplitudeExponent steps := by
  obtain ⟨j,hj⟩ := exists_nat_gt (10*((N : ℝ)+R+1))
  have hpow : 1+(j : ℝ)/5 ≤ (6/5 : ℝ)^j := by
    convert one_add_mul_le_pow (a := (1/5 : ℝ)) (by norm_num) j using 1 <;> ring
  refine ⟨j+1,by omega,?_⟩
  rw [amplitudeExponent_succ]
  have hp : 0 < (6/5 : ℝ)^j := by positivity
  dsimp [amplitudeExponent]
  nlinarith

/-- The loss powers determine one slow exponent before choosing the finite
substitution accuracies in the primitive realization argument. -/
theorem exists_slow_exponent (R N L : ℕ) (hL : N+R < L) (p p₁ : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ σ*(p₁+2) < 1 ∧ σ*p < 1/2 ∧
      σ < 1/16 ∧ (L : ℝ)-R-σ*p₁ > N := by
  have hgap : 0 < (L : ℝ)-R-N := by
    have hh : (N : ℝ)+R < L := by exact_mod_cast hL
    linarith
  obtain ⟨η₁,hη₁,_,hb₁⟩ := ExactCorrection.positive_power_threshold (p₁+2) 1 1
    zero_lt_one zero_lt_one
  obtain ⟨η₂,hη₂,_,hb₂⟩ := ExactCorrection.positive_power_threshold p 1 (1/2)
    zero_lt_one (by norm_num)
  obtain ⟨η₃,hη₃,_,hb₃⟩ := ExactCorrection.positive_power_threshold p₁ 1
    ((L : ℝ)-R-N) zero_lt_one hgap
  let η := min (1/32) (min η₁ (min η₂ η₃))
  have hη : 0 < η := lt_min (by norm_num) (lt_min hη₁ (lt_min hη₂ hη₃))
  let σ := η/2
  have hσ : 0 < σ := half_pos hη
  have hση : σ < η := half_lt_self hη
  have hσ32 : σ < 1/32 := hση.trans_le (min_le_left _ _)
  have hσ₁ : σ < η₁ := hση.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hσ₂ : σ < η₂ := hση.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hσ₃ : σ < η₃ := hση.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h₁ := hb₁ σ hσ hσ₁
  have h₂ := hb₂ σ hσ hσ₂
  have h₃ := hb₃ σ hσ hσ₃
  simp only [Real.rpow_one] at h₁ h₂ h₃
  refine ⟨σ,hσ,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma scaleExponent_bounds {σ : ℝ} (hσ : 0 < σ) {steps j : ℕ}
    (hs : 1 ≤ steps) (hj : j ≤ steps) :
    0 ≤ scaleExponent σ steps j ∧ scaleExponent σ steps j ≤ σ := by
  have hs' : 0 < (steps : ℝ) := by exact_mod_cast (by omega : 0 < steps)
  have hj' : (j : ℝ) ≤ steps := by exact_mod_cast hj
  unfold scaleExponent
  constructor
  · positivity
  · apply (div_le_iff₀ hs').mpr
    nlinarith

lemma scaleExponent_step {σ : ℝ} {steps j : ℕ} :
    scaleExponent σ steps (j+1)-scaleExponent σ steps j = σ/(steps : ℝ) := by
  simp only [scaleExponent,Nat.cast_add,Nat.cast_one]
  ring

/-- Both the normalized cubic remainder and the C3 displacement decay at
every stage of the finite slow iteration. -/
theorem slow_step_positive_powers {σ : ℝ} (hσ : 0 < σ) (hσsmall : σ < 1/16)
    {steps j : ℕ} (hs : 1 ≤ steps) (hj : j < steps) :
    0 < 3*amplitudeExponent j-scaleExponent σ steps (j+1)-2*amplitudeExponent (j+1) ∧
    0 < amplitudeExponent j-2*scaleExponent σ steps (j+1) ∧
    0 < min (σ/(steps : ℝ)) (1/2) := by
  have he := (scaleExponent_bounds hσ hs (Nat.succ_le_of_lt hj)).2
  have hd := amplitudeExponent_lower j
  have hs' : 0 < (steps : ℝ) := by exact_mod_cast (by omega : 0 < steps)
  rw [amplitudeExponent_succ]
  refine ⟨by linarith,by linarith,lt_min (div_pos hσ hs') (by norm_num)⟩

/-- Accuracy orders can be chosen after all scale and loss exponents are
fixed; this prevents a circular dependence of the slow scale on accuracy. -/
theorem exists_step_accuracy {κ : ℝ} (hκ : 0 < κ) (j : ℕ) :
    ∃ q : ℕ, amplitudeExponent j+κ*q > 2*amplitudeExponent (j+1) := by
  obtain ⟨q,hq⟩ := exists_nat_gt ((2*amplitudeExponent (j+1)-amplitudeExponent j)/κ)
  refine ⟨q,?_⟩
  have hh := (div_lt_iff₀ hκ).mp hq
  nlinarith

/-- The perturbed mean parameter has a positive decay exponent independent
of the accuracy order chosen at this stage. -/
theorem slow_parameter_bound {σ p z : ℝ} (hσ : 0 < σ) (hp : 0 ≤ p)
    (hσp : σ*p < 1/2) (hz : 0 < z) (hz1 : z ≤ 1)
    {steps j : ℕ} (hs : 1 ≤ steps) (hj : j < steps) :
    z^(scaleExponent σ steps (j+1))/z^(scaleExponent σ steps j)+
      z/(z^(scaleExponent σ steps (j+1)))^p ≤
        2*z^(min (σ/(steps : ℝ)) (1/2)) := by
  let κ := min (σ/(steps : ℝ)) (1/2)
  have hscale := (scaleExponent_bounds hσ hs (Nat.succ_le_of_lt hj)).2
  have hgap : κ ≤ 1-scaleExponent σ steps (j+1)*p := by
    have hm := mul_le_mul_of_nonneg_right hscale hp
    have hk : κ ≤ 1/2 := min_le_right _ _
    linarith
  have hfirst : z^(σ/(steps : ℝ)) ≤ z^κ :=
    Real.rpow_le_rpow_of_exponent_ge hz hz1 (min_le_left _ _)
  have hsecond : z^(1-scaleExponent σ steps (j+1)*p) ≤ z^κ :=
    Real.rpow_le_rpow_of_exponent_ge hz hz1 hgap
  rw [← Real.rpow_sub hz,scaleExponent_step,← Real.rpow_mul hz.le]
  have hratio (a : ℝ) : z/z^a = z^(1-a) := by
    rw [Real.rpow_sub hz,Real.rpow_one]
  rw [hratio]
  linarith

/-- A small-increment error with the paper's two terms becomes arbitrarily
small after division by the next amplitude squared. This is the finite
inductive step used to improve the primitive's metric accuracy. -/
theorem normalized_slow_error_threshold {d d' b κ C e : ℝ} {q : ℕ}
    (hC : 0 ≤ C) (he : 0 < e)
    (ha : 0 < d+κ*q-2*d') (hb : 0 < 3*d-b-2*d') :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < ζ →
      ∀ η : ℝ, 0 ≤ η → η ≤ 2*z^κ →
      (C*(z^d*η^q+(z^d)^3/z^b))/(z^d')^2 < e := by
  obtain ⟨ζ₁,hζ₁,hζ₁1,h₁⟩ := ExactCorrection.positive_power_threshold
    (C*2^q) (d+κ*q-2*d') (e/2) ha (half_pos he)
  obtain ⟨ζ₂,hζ₂,_,h₂⟩ := ExactCorrection.positive_power_threshold
    C (3*d-b-2*d') (e/2) hb (half_pos he)
  refine ⟨min ζ₁ ζ₂,lt_min hζ₁ hζ₂,(min_le_left _ _).trans hζ₁1,?_⟩
  intro z hz hzζ η hη hηb
  have hpa : z^d*(z^κ)^q/(z^d')^2 = z^(d+κ*q-2*d') := by
    simpa only [Real.rpow_zero,div_one,Real.rpow_natCast,sub_zero] using
      ExactCorrection.scale_ratio_power hz d κ 0 (q : ℝ) d'
  have hpb := ExactCorrection.scale_cubic_quotient hz d b d'
  have hbound : (C*(z^d*η^q+(z^d)^3/z^b))/(z^d')^2 ≤
      (C*2^q)*z^(d+κ*q-2*d')+C*z^(3*d-b-2*d') := by
    calc
      _ ≤ (C*(z^d*(2*z^κ)^q+(z^d)^3/z^b))/(z^d')^2 := by
        gcongr
      _ = (C*2^q)*(z^d*(z^κ)^q/(z^d')^2)+
          C*(((z^d)^3/z^b)/(z^d')^2) := by rw [mul_pow]; ring
      _ = _ := by rw [hpa,hpb]
  exact hbound.trans_lt (by
    have h₁' := h₁ z hz (hzζ.trans_le (min_le_left _ _))
    have h₂' := h₂ z hz (hzζ.trans_le (min_le_right _ _))
    linarith)

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
