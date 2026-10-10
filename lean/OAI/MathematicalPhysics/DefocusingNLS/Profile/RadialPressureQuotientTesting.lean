import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureTesting

namespace OAI

/-! Removing the limiting amplitude factor gives the pressure's C1 test limit. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_bounded_mul_zero {s : Set ℝ} (B C : ℕ → ℝ → ℝ)
    (hB : ∀ n r, r ∈ s → ‖B n r‖ ≤ 1)
    (hC : TendstoUniformlyOn C (fun _ => 0) atTop s) :
    TendstoUniformlyOn (fun n r => B n r*C n r) (fun _ => 0) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hC ⊢
  intro ε hε
  filter_upwards [hC ε hε] with n hn r hr
  rw [dist_zero_left,norm_mul]
  have hc : ‖C n r‖ < ε := by simpa only [dist_zero_left] using hn r hr
  exact (mul_le_mul_of_nonneg_right (hB n r hr) (norm_nonneg _)).trans_lt
    (by simpa only [one_mul] using hc)

theorem radial_pressure_quotient_test_convergence (R l b : ℝ) (hl : 0 ≤ l) (hlR : l ≤ R)
    (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n) (H : ℕ → ℝ → ℝ) (hH : ∀ n, Continuous (H n))
    (hH0 : ∀ n r, r ∈ Icc 0 R → 0 ≤ H n r)
    (hP : ∀ n r, r ∈ Icc 0 R → (H n r)^(p n-1) ≤ 1)
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D) (hAz : ∀ r, A r ≠ 0)
    (hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r)
    (hcore : EqOn A (fun _ => 1) (Icc 0 l))
    (hTA : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hT : TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, (H n t)^(p n)*t^11)
      (fun r => b/12*(min r l)^12) atTop (Icc 0 R))
    (φ φ₁ : ℝ → ℝ) (hφ : Continuous φ) (hφ₁ : Continuous φ₁)
    (hφD : ∀ r ∈ Ioo 0 R, HasDerivAt φ (φ₁ r) r) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..R, (H n t)^(p n-1)*φ t*t^11) atTop
      (𝓝 (b*∫ t in (0 : ℝ)..l, φ t*t^11)) := by
  let θ := fun r => φ r/A r
  let θ₁ := fun r => (φ₁ r*A r-φ r*D r)/(A r)^2
  have hθ : Continuous θ := hφ.div hA hAz
  have hθ₁ : Continuous θ₁ := ((hφ₁.mul hA).sub (hφ.mul hD)).div (hA.pow 2)
    (fun r => pow_ne_zero 2 (hAz r))
  have hθD : ∀ r ∈ Ioo 0 R, HasDerivAt θ (θ₁ r) r :=
    fun r hr => (hφD r hr).div (hAD r hr) (hAz r)
  have hAmp := radial_pressure_amplitude_test_convergence R l b hl hlR p H hH hT
    θ θ₁ hθ hθ₁ hθD
  have hθcore : (∫ t in (0 : ℝ)..l, θ t*t^11)=∫ t in (0 : ℝ)..l, φ t*t^11 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc 0 l := uIcc_of_le hl ▸ ht
    change φ t/A t*t^11=φ t*t^11
    rw [hcore htI,div_one]
  rw [hθcore] at hAmp
  have hθT : TendstoUniformlyOn (fun _ : ℕ => θ) θ atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hφT : TendstoUniformlyOn (fun _ : ℕ => φ) φ atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hHT := radial_uniform_product R H (fun _ => θ) A θ hTA hθT hA.continuousOn hθ.continuousOn
  have hrem : TendstoUniformlyOn (fun n r => φ r-H n r*θ r) (fun _ => 0) atTop (Icc 0 R) := by
    apply (hφT.sub hHT).congr_right
    intro r _
    dsimp [θ]
    field_simp [hAz r]
    ring
  have hBP : ∀ n r, r ∈ Icc 0 R → ‖(H n r)^(p n-1)‖ ≤ 1 := by
    intro n r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hH0 n r hr) _)]
    exact hP n r hr
  have hremT := radial_bounded_mul_zero (fun n r => (H n r)^(p n-1))
    (fun n r => φ r-H n r*θ r) hBP hrem
  have hI := radial_weighted_integral_uniform R (hl.trans hlR)
    (fun n r => (H n r)^(p n-1)*(φ r-H n r*θ r)) (fun _ => 0)
    (fun n => (((hH n).pow _).mul (hφ.sub ((hH n).mul hθ))).continuousOn)
    continuousOn_const hremT
  have hI0 := hI.tendsto_at (show R ∈ Icc 0 R from ⟨hl.trans hlR,le_rfl⟩)
  simp only [zero_mul,intervalIntegral.integral_zero] at hI0
  have hout := hAmp.add hI0
  simp only [add_zero] at hout
  apply hout.congr'
  apply Eventually.of_forall
  intro n
  change (∫ t in (0 : ℝ)..R, (H n t)^(p n)*θ t*t^11)+
    (∫ t in (0 : ℝ)..R, (H n t)^(p n-1)*(φ t-H n t*θ t)*t^11)=_
  rw [← intervalIntegral.integral_add (μ := volume)
    (f := fun t => (H n t)^(p n)*θ t*t^11)
    (g := fun t => (H n t)^(p n-1)*(φ t-H n t*θ t)*t^11)
    ((((hH n).pow (p n)).mul hθ).mul (continuous_id.pow 11) |>.intervalIntegrable 0 R)
    (((((hH n).pow (p n-1)).mul (hφ.sub ((hH n).mul hθ))).mul
      (continuous_id.pow 11)).intervalIntegrable 0 R)]
  apply intervalIntegral.integral_congr
  intro t _
  change (H n t)^(p n)*θ t*t^11+(H n t)^(p n-1)*(φ t-H n t*θ t)*t^11=
    (H n t)^(p n-1)*φ t*t^11
  have hpow : (H n t)^(p n)=(H n t)^(p n-1)*H n t := by
    rw [← pow_succ]
    congr 1
    have hn := hp n
    omega
  rw [hpow]
  ring

end DefocusingNLS

end OAI
