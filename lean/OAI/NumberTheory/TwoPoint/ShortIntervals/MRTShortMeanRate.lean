import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFirstResolution
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCommonFinalBand

namespace OAI

/-! Independent height and short-length thresholds for the final scalar
MRT rate. The density remains linear and the logarithmic energy error
has the published exponent after taking its square root. -/

namespace TwoPointCorrelations

open Filter

lemma mrt_three_square_envelope (a b x y z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    a*x^2+b*y^2+b*z^2  ≤  (a+b)*(x+y+z)^2 := by
  have hs : x^2+y^2+z^2  ≤  (x+y+z)^2 := by
    nlinarith [mul_nonneg hx hy,mul_nonneg hx hz,mul_nonneg hy hz]
  have ht : a*x^2+b*y^2+b*z^2  ≤  (a+b)*(x^2+y^2+z^2) := by
    nlinarith [mul_nonneg hb (sq_nonneg x),mul_nonneg ha (sq_nonneg y),
      mul_nonneg ha (sq_nonneg z)]
  exact ht.trans (mul_le_mul_of_nonneg_left hs (add_nonneg ha hb))

/-- The elementary kernel and finite endpoint terms fit the square of
`loglog(H)/log(H)`, with a threshold only on the short length. -/
lemma mrt_first_kernel_square_rate (A : ℕ) (hA : 500000 ≤ A) :
    ∀ᶠ H : ℝ in atTop,
      0 ≤ Real.log (Real.log H)/Real.log H ∧
      0 ≤ Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H) ∧
      Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H)  ≤
        (10*(A:ℝ))*(Real.log (Real.log H)/Real.log H) ∧
      33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
        (minorArcFirstUpper H) (1/100))⁻¹ + 2*(minorArcFirstLower A H)⁻¹ +
      1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
        (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H)  ≤
        (33792*Real.exp 1+2+2048*Real.exp 2)*(Real.log (Real.log H)/Real.log H)^2 ∧
      1/H^2  ≤  (Real.log (Real.log H)/Real.log H)^2 := by
  have hp := (Real.isLittleO_pow_log_id_atTop (n:=50)).bound (show (0:ℝ)<1 by norm_num)
  filter_upwards [mrt_first_kernel_error_eventually A hA,
    minor_arc_first_band_scale A 0 (by omega),
    minor_arc_first_band_density_eventually A (by omega),hp] with H hk hscale hratio hpow
  obtain ⟨hH,hLH,hLL,hP,_,_,hPQ,_,_,hQ⟩ := hscale
  have hH0 : 0<H := by linarith
  have hL0 : 0<Real.log H := by linarith
  have hL1 : 1 ≤ Real.log H := by linarith
  have hpow' : (Real.log H)^50 ≤ H := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hL0.le 50),
      abs_of_pos hH0,one_mul] using hpow
  have h100 : (Real.log H)^100 ≤ H^2 := by
    have hh := pow_le_pow_left₀ (pow_nonneg hL0.le 50) hpow' 2
    simpa only [← pow_mul] using hh
  have hinv : 1/(Real.log H)^100  ≤  (Real.log (Real.log H)/Real.log H)^2 := by
    calc
      _  ≤  1/(Real.log H)^2 := one_div_le_one_div_of_le (pow_pos hL0 2)
        (pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 100))
      _  ≤  (Real.log (Real.log H))^2/(Real.log H)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact one_le_pow₀ hLL
      _ = _ := (div_pow _ _ _).symm
  have hnorm : 0 ≤ Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H) :=
    div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  refine ⟨div_nonneg (by linarith) hL0.le,hnorm,?_,?_,?_⟩
  · convert hratio using 1
    ring
  · apply hk.trans
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hinv
        (show 0 ≤ 33792*Real.exp 1+2+2048*Real.exp 2 by positivity)
  · exact (one_div_le_one_div_of_le (pow_pos hL0 100) h100).trans hinv

/-- The exact scalar expression in `halasz_actual_short_mean` has the
required rate with independent absolute-scale and short-length thresholds. -/
theorem mrt_short_mean_rate (A : ℕ) (hA : 500000 ≤ A) (C₁ C₂ : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C L₀ H₀ : ℝ, 0<C ∧ 1 ≤ L₀ ∧ 1 ≤ H₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ H : ℝ, H₀ ≤ H → ∀ M : ℝ,
      Real.sqrt ((139968/(2*Real.pi)) *
        (12*(C₁*((Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H))^2+
            Real.exp (-M)+Real.log L/L^(1/100:ℝ)) +
          33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
            (minorArcFirstUpper H) (1/100))⁻¹ + 2*(minorArcFirstLower A H)⁻¹ +
          1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
            (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H)) +
          128*Real.exp 1/H^2)) +
        C₂*(Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H))  ≤
      C*(Real.log (Real.log H)/Real.log H + Real.exp (-M/2)+L^(-1/700:ℝ)) := by
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp mrt_log_error_published_rate
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (mrt_first_kernel_square_rate A hA)
  let D : ℝ := 33792*Real.exp 1+2+2048*Real.exp 2
  let a : ℝ := 12*C₁*(10*(A:ℝ))^2+12*D+128*Real.exp 1
  let b : ℝ := 12*C₁
  let V : ℝ := (139968/(2*Real.pi))*(a+b)
  let C : ℝ := Real.sqrt V+C₂*(10*(A:ℝ))+1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,max L₀ 1,max H₀ 1,hC,le_max_right _ _,le_max_right _ _,?_⟩
  intro L hL H hH M
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0<L := by linarith
  obtain ⟨hδ,_⟩ := hL₀ L ((le_max_left _ _).trans hL)
  obtain ⟨hr,hR,hRr,hkernel,hendpoint⟩ := hH₀ H ((le_max_left _ _).trans hH)
  let r := Real.log (Real.log H)/Real.log H
  let R := Real.log (minorArcFirstLower A H)/Real.log (minorArcFirstUpper H)
  let e := Real.exp (-M/2)
  let s := L^(-1/700:ℝ)
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hs : 0 ≤ s := Real.rpow_nonneg hL0.le _
  have hR2 : R^2 ≤ (10*(A:ℝ))^2*r^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hR hRr 2
  have he2 : Real.exp (-M)=e^2 := by
    dsimp [e]
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hs2 : L^(-1/350:ℝ)=s^2 := by
    dsimp [s]
    rw [← Real.rpow_natCast,← Real.rpow_mul hL0.le]
    norm_num
  rw [hs2] at hδ
  have hi : 12*(C₁*(R^2+Real.exp (-M)+Real.log L/L^(1/100:ℝ))+
        (33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
          (minorArcFirstUpper H) (1/100))⁻¹+2*(minorArcFirstLower A H)⁻¹+
        1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
          (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H)))+
        128*Real.exp 1/H^2  ≤  a*r^2+b*e^2+b*s^2 := by
    have ht := mul_le_mul_of_nonneg_left hendpoint (show 0 ≤ 128*Real.exp 1 by positivity)
    have hm := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hR2 (le_refl (Real.exp (-M)))) hδ) hC₁
    rw [he2] at hm
    have hh := mul_le_mul_of_nonneg_left (add_le_add hm hkernel) (show (0:ℝ) ≤ 12 by norm_num)
    rw [he2]
    convert add_le_add hh ht using 1
    · ring
    · dsimp only [a,b,D,r]
      ring
  have hroot : Real.sqrt ((139968/(2*Real.pi))*
      (12*(C₁*(R^2+Real.exp (-M)+Real.log L/L^(1/100:ℝ))+
        (33792*Real.exp 1*(mrtBaseResolution (minorArcFirstLower A H)
          (minorArcFirstUpper H) (1/100))⁻¹+2*(minorArcFirstLower A H)⁻¹+
        1024*Real.exp 2*(mrtBaseResolution (minorArcFirstLower A H)
          (minorArcFirstUpper H) (1/100))⁻¹*(1+minorArcFirstUpper H/H)))+
        128*Real.exp 1/H^2))  ≤  Real.sqrt V*(r+e+s) := by
    have hsum := mrt_three_square_envelope a b r e s ha hb hr he hs
    calc
      _  ≤  Real.sqrt ((139968/(2*Real.pi))*((a+b)*(r+e+s)^2)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hi.trans hsum) (by positivity))
      _ = _ := by
        rw [← mul_assoc,Real.sqrt_mul hV,Real.sqrt_sq (by positivity : 0 ≤ r+e+s)]
  change 0 ≤ r at hr
  have hlinear := mul_le_mul_of_nonneg_left hRr hC₂
  change C₂*R ≤ C₂*((10*(A:ℝ))*r) at hlinear
  have hremaining : 0 ≤ C₂*(10*(A:ℝ))*(e+s) := by positivity
  calc
    _ ≤ Real.sqrt V*(r+e+s)+C₂*R := by
      simpa only [add_assoc] using add_le_add hroot (le_refl (C₂*R))
    _ ≤ C*(r+e+s) := by
      dsimp [C]
      nlinarith

end TwoPointCorrelations

end OAI
