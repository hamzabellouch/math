import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularCertificate

namespace OAI

/-! The positive multiplier potential on the straight part of the high-angular contour. -/

namespace DefocusingNLS

noncomputable def highRayU (t : ℝ) : ℝ := 10/101+(99/101)*t
noncomputable def highRayV (Z t : ℝ) : ℝ := Z+1/101+(20/101)*t
noncomputable def highRayL (Z t : ℝ) : ℝ :=
  ((9401 : ℝ)*highRayU t+3960*highRayV Z t)/10201

noncomputable def highRayPotential (σ M Z t : ℝ) : ℝ :=
  σ-3+highRayU t/4+
    M^2*highRayU t/(4*(highRayU t^2+highRayV Z t^2))+
    5/(1+(3/2)*t)^2-(-3/2+(11/4)*t)^2/(highRayL Z t*(1+(3/2)*t)^2)

theorem highRay_bounds (Z t : ℝ) (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000)
    (ht : 0 ≤ t) :
    99/1000+(98/100)*t ≤ highRayU t ∧
    highRayU t ≤ 1/10+(981/1000)*t ∧
    0 < highRayV Z t ∧ highRayV Z t ≤ 272/100+(1/5)*t ∧
    113/100+(98/100)*t ≤ highRayL Z t := by
  dsimp only [highRayU,highRayV,highRayL]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem highRayPotential_pos (σ M Z t : ℝ)
    (hσ : -(1/32 : ℝ) ≤ σ) (hM : 9 ≤ M)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) (ht : 0 ≤ t) :
    0 < highRayPotential σ M Z t := by
  let u₀ : ℝ := 99/1000+(98/100)*t
  let L₀ : ℝ := 113/100+(98/100)*t
  let d₀ : ℝ := (1/10+(981/1000)*t)^2+(272/100+(1/5)*t)^2
  let q₀ : ℝ := 1+(3/2)*t
  let A : ℝ := -3/2+(11/4)*t
  obtain ⟨hu,hu',hv,hv',hL⟩ := highRay_bounds Z t hZ hZ' ht
  have huBound : u₀ ≤ highRayU t := hu
  have hu₀ : 0 < u₀ := by dsimp [u₀]; positivity
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  have hq₀ : 0 < q₀ := by dsimp [q₀]; positivity
  have huPos : 0 < highRayU t := lt_of_lt_of_le hu₀ hu
  have hD : 0 < highRayU t^2+highRayV Z t^2 := by positivity
  have hDb : highRayU t^2+highRayV Z t^2 ≤ d₀ := by
    have huSq := (sq_le_sq₀ huPos.le (by positivity : 0 ≤ 1/10+(981/1000)*t)).mpr hu'
    have hvSq := (sq_le_sq₀ hv.le (by positivity : 0 ≤ 272/100+(1/5)*t)).mpr hv'
    exact add_le_add huSq hvSq
  have hLPos : 0 < highRayL Z t := lt_of_lt_of_le hL₀ hL
  have hM2 : 81 ≤ M^2 := by nlinarith
  have hAngular : 81*u₀/(4*d₀) ≤
      M^2*highRayU t/(4*(highRayU t^2+highRayV Z t^2)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hnum : 81*u₀ ≤ M^2*highRayU t :=
      mul_le_mul hM2 hu hu₀.le (sq_nonneg M)
    have hprod := mul_le_mul (show 4*(highRayU t^2+highRayV Z t^2) ≤ 4*d₀ by linarith)
      hnum (by positivity) (by positivity)
    nlinarith
  have hNegative : A^2/(highRayL Z t*q₀^2) ≤ A^2/(L₀*q₀^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (sq_nonneg _))
      (sq_nonneg A)
  let V₀ : ℝ := -3-1/32+u₀/4+81*u₀/(4*d₀)+5/q₀^2-A^2/(L₀*q₀^2)
  have hV : V₀ ≤ highRayPotential σ M Z t := by
    change -3-1/32+u₀/4+81*u₀/(4*d₀)+5/q₀^2-A^2/(L₀*q₀^2) ≤
      σ-3+highRayU t/4+M^2*highRayU t/(4*(highRayU t^2+highRayV Z t^2))+
        5/q₀^2-A^2/(highRayL Z t*q₀^2)
    linarith
  have hP : V₀*L₀*d₀*q₀^2 = highAngularPolynomial t := by
    dsimp only [V₀,highAngularPolynomial,u₀,L₀,d₀,q₀,A]
    field_simp [ne_of_gt hd₀,ne_of_gt hL₀,ne_of_gt hq₀]
  have hpos := highAngularPolynomial_pos ht
  rw [← hP] at hpos
  have hV₀ : 0 < V₀ := by
    have h₃ := (mul_pos_iff_of_pos_right (sq_pos_of_pos hq₀)).mp hpos
    have h₂ := (mul_pos_iff_of_pos_right hd₀).mp h₃
    exact (mul_pos_iff_of_pos_right hL₀).mp h₂
  exact lt_of_lt_of_le hV₀ hV

end DefocusingNLS

end OAI
