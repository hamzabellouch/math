import OAI.MeasureTheory.Falconer.Angular.RetainedSmallSphere
import OAI.MeasureTheory.Falconer.Fourier.JetStateFarRemainder

namespace OAI

/-! # The actual noncomparable two-sphere kernel

The small sphere is never expanded. Only the large sphere incurs a
stationary remainder, and its bound uses the two existing published inputs.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem noncomparable_leading_decay_mono (m q : ℕ) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) :
    y^(-((m+2:ℕ):ℝ)/2)/(y/2)^q ≤ x^(-((m+2:ℕ):ℝ)/2)/(x/2)^q := by
  have hy : 0 < y := hx.trans_le hxy
  have hp : -((m+2:ℕ):ℝ)/2 ≤ 0 := by
    have hn : 0 ≤ ((m+2:ℕ):ℝ) := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ x^(-((m+2:ℕ):ℝ)/2)/(y/2)^q := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hx hxy hp) (pow_nonneg (by positivity) _)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _)
      (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) (by linarith) _)

theorem exists_noncomparable_sphere_kernel
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J q : ℕ) (hJ : 1 ≤ J) {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ H S : ℝ, 0 ≤ H ∧ 0 ≤ S ∧
      ∀ (B : Space (m+3) → ℂ), ContDiff ℝ ∞ B →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ k B w‖ ≤ C*D^k) →
      ∀ (G : Sphere (m+3) → ℂ), Measurable G →
      ∀ E : ℝ, 0 ≤ E → (∀ w, ‖G w‖ ≤ E) →
      ∀ (e f : Sphere (m+3)) (v large small base κ : ℝ),
      0 < large → 0 ≤ small → 2*small ≤ large → 1 ≤ base →
      D^2 ≤ (2:ℝ)^v*large → D ≤ base^2 →
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        1 ≤ r*large ∧ D^2/(r*large) ≤ base^(-κ)) →
      let ε := S*C*base^(-κ*(J:ℝ)+2*(m+3))
      ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, (Ψ (r/(2:ℝ)^v):ℂ)*
        sphereOscillation (r*large) e (fun w => B w)*sphereOscillation (r*small) f G)‖ ≤
        H*C*E*(sphereMeasure (m+3)).real univ*
          ((2:ℝ)^v*large)^(-((m+2:ℕ):ℝ)/2)/((2:ℝ)^v*large/2)^q +
        4*W*(ε*(2*(max C E*(sphereMeasure (m+3)).real univ)+ε)) := by
  obtain ⟨H,hH,hleading⟩ := single_sphere_retained_bound hΨ hs m J q
  obtain ⟨S,hS,hstationary⟩ := sphere_stationary_expansion_unscaled hgnomonic hquadratic m J hJ
  refine ⟨H,S,hH,hS,?_⟩
  intro B hB C D hC hD hb G hG E hE hGE e f v large small base κ
    hl hsmall hsep hbase hlead hDbase hregime
  let ε := S*C*base^(-κ*(J:ℝ)+2*(m+3))
  let A₀ := fun r => sphereOscillation (r*large) e (fun w => B w)
  let B₀ := fun r => sphereOscillation (r*small) f G
  let A₁ := fun r => stationarySphereApprox m J (r*large) B e
  let C₀ := max C E*(sphereMeasure (m+3)).real univ
  have hC₀ : 0 ≤ C₀ := mul_nonneg (hC.trans (le_max_left _ _)) measureReal_nonneg
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hBm : Measurable (fun w : Sphere (m+3) => B w) :=
    hB.continuous.measurable.comp continuous_subtype_val.measurable
  have hmA : Measurable A₀ := (sphereOscillation_frequency_measurable e _ hBm).comp (by fun_prop)
  have hmB : Measurable B₀ := (sphereOscillation_frequency_measurable f G hG).comp (by fun_prop)
  have hmA₁ : Measurable A₁ := (stationarySphereApprox_frequency_measurable m J B e).comp (by fun_prop)
  have hBbound (w : Sphere (m+3)) : ‖B w‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb 0 (by omega) w
  have hAbound (r : ℝ) : ‖A₀ r‖ ≤ C₀ :=
    (sphereOscillation_norm_le_of_bound _ _ _ hBbound).trans
      (mul_le_mul_of_nonneg_right (le_max_left C E) measureReal_nonneg)
  have hB₀bound (r : ℝ) : ‖B₀ r‖ ≤ C₀ :=
    (sphereOscillation_norm_le_of_bound _ _ _ hGE).trans
      (mul_le_mul_of_nonneg_right (le_max_right C E) measureReal_nonneg)
  have herror (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) : ‖A₀ r-A₁ r‖ ≤ ε := by
    obtain ⟨hΛ,hscale⟩ := hregime r hr
    have hraw := hstationary e B hB C D hC hD hb (r*large) hΛ
    have hp := stationary_sphere_remainder_scale m J hbase (zero_le_one.trans hD) hΛ hDbase hscale
    apply hraw.trans
    calc
      _ = (S*C)*((r*large)^(-(J:ℝ)-((m+2:ℕ):ℝ)/2)*D^(2*J+(m+2)+1)) := by ring
      _ ≤ ε := mul_le_mul_of_nonneg_left hp (mul_nonneg hS hC)
  have hreplace := PlanarFalconer.angular_radial_product_replacement v hΨ.continuous.measurable
    hpos hs hW hΨW A₀ B₀ A₁ B₀ hmA hmB hmA₁ hmB hC₀ hε hAbound hB₀bound
    herror (fun r _ => by simpa using hε)
  have hleadBound := hleading B hB C D ((2:ℝ)^v) large small E hC hD
    (Real.rpow_pos_of_pos (by norm_num) _) hl hsmall hsep hlead
    (fun k hk => hb k (by omega)) e f G hG hGE
  have hscale : ((2:ℝ)^v)⁻¹ •
      (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r)) =
      ∫ s : ℝ, (Ψ s:ℂ)*stationarySphereApprox m J ((2:ℝ)^v*s*large) B e*
        sphereOscillation ((2:ℝ)^v*s*small) f G := by
    have h := Measure.integral_comp_mul_left
      (fun r : ℝ => Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r)) ((2:ℝ)^v)
    have hR : 0 < (2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
    simpa only [mul_div_cancel_left₀ _ hR.ne',abs_of_pos hR,
      abs_of_pos (inv_pos.mpr hR),A₁,B₀,Complex.real_smul,mul_assoc] using h.symm
  have hsum : ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₀ r*B₀ r))‖ ≤
      ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r))‖ +
        4*W*(ε*(2*C₀+ε)) := by
    let X := ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₀ r*B₀ r))
    let Y := ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, Ψ (r/(2:ℝ)^v) • (A₁ r*B₀ r))
    have htriangle : ‖X‖ ≤ ‖Y‖+‖X-Y‖ := by
      calc
        _ = ‖Y+(X-Y)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    exact htriangle.trans (add_le_add le_rfl hreplace)
  rw [hscale] at hsum
  have htotal := hsum.trans (add_le_add hleadBound le_rfl)
  simpa only [A₀,B₀,Complex.real_smul,mul_assoc,ε,C₀] using htotal

end Falconer

end OAI
