import Mathlib

namespace OAI

/-! Circle domains, conformal removability, and conditional analytic rigidity from length and area estimates. -/

noncomputable section
open Set Classical
open scoped OnePoint

namespace CircleDomainRigidity

abbrev Sphere := OnePoint ℂ
abbrev Mobius := Matrix.GeneralLinearGroup (Fin 2) ℂ

def sphereInv (p : Sphere) : Sphere :=
  p.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

def finiteCoord (p : Sphere) : ℂ := p.elim 0 id

def chart (p q : Sphere) : ℂ :=
  if p = ∞ then finiteCoord (sphereInv q) else finiteCoord q

def chartSymm (p : Sphere) (z : ℂ) : Sphere :=
  if p = ∞ then sphereInv (z : Sphere) else (z : Sphere)

def IsConformalAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ∃ d : ℂ, d ≠ 0 ∧
    HasDerivAt (fun z ↦ chart (f p) (f (chartSymm p z))) d (chart p p)

def IsConformalOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsConformalAt f p

def IsConformalEquivalence (f : Sphere → Sphere) (U V : Set Sphere) : Prop :=
  IsConformalOn f U ∧ MapsTo f U V ∧ ∃ g : Sphere → Sphere,
    IsConformalOn g V ∧ MapsTo g V U ∧
    (∀ z ∈ U, g (f z) = z) ∧ (∀ w ∈ V, f (g w) = w)

def IsRoundClosedDisk (K : Set Sphere) : Prop :=
  ∃ M : Mobius,
    K = (fun p : Sphere ↦ M • p) ''
      (((↑) : ℂ → Sphere) '' Metric.closedBall (0 : ℂ) 1)

def IsCircleDomain (U : Set Sphere) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ p ∈ Uᶜ, (∃ q : Sphere, connectedComponentIn Uᶜ p = {q}) ∨
      IsRoundClosedDisk (connectedComponentIn Uᶜ p)

def OrientationPreserving (h : Sphere ≃ₜ Sphere) : Prop :=
  ContinuousMap.Homotopic (⟨h, h.continuous⟩ : C(Sphere, Sphere)) (ContinuousMap.id Sphere)

def IsConformallyRemovable (E : Set Sphere) : Prop :=
  IsCompact E ∧ ∀ h : Sphere ≃ₜ Sphere, OrientationPreserving h →
    IsConformalOn h Eᶜ → ∃ M : Mobius, ∀ p : Sphere, h p = M • p

theorem IsConformalOn.mono {f : Sphere → Sphere} {U V : Set Sphere}
    (hf : IsConformalOn f U) (hVU : V ⊆ U) : IsConformalOn f V :=
  fun p hp ↦ hf p (hVU hp)

theorem IsConformallyRemovable.of_isCompact_subset {E K : Set Sphere}
    (hE : IsConformallyRemovable E) (hK : IsCompact K) (hKE : K ⊆ E) :
    IsConformallyRemovable K := by
  refine ⟨hK, fun h hor hconf ↦ ?_⟩
  exact hE.2 h hor (hconf.mono (compl_subset_compl.mpr hKE))

theorem isCircleDomain_univ : IsCircleDomain (univ : Set Sphere) := by
  refine ⟨isOpen_univ, isConnected_univ, ?_⟩
  intro p hp
  simp only [compl_univ, mem_empty_iff_false] at hp

end CircleDomainRigidity

open MeasureTheory Filter Bornology
open scoped Topology
namespace CircleDomainRigidity.LengthArea

theorem summable_mul_of_squares {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2)) :
    Summable (fun j ↦ r j * s j) := by
  apply (hr.add hs).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|r j| - |s j|), sq_abs (r j), sq_abs (s j),
    sq_nonneg (r j), sq_nonneg (s j)]

theorem hasSum_square_discrepancy {ι : Type*} {r s : ι → ℝ}
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2)) :
    HasSum (fun j ↦ (r j - s j) ^ 2)
      ((∑' j, r j ^ 2) - 2 * (∑' j, r j * s j) + (∑' j, s j ^ 2)) := by
  have hp := summable_mul_of_squares hr hs
  convert! (hr.hasSum.sub (hp.hasSum.mul_left 2)).add hs.hasSum using 1
  ext j
  ring

theorem discrepancy_nonpos {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} {r s : ι → ℝ} {A : ℝ}
    (hu : Integrable u μ) (hu2 : Integrable (fun x ↦ u x ^ 2) μ)
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _, (1 : ℝ) ∂μ) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ x, u x ^ 2 ∂μ) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ x, u x ∂μ) + 2 * Real.pi * (∑' j, r j * s j)) :
    (∫ x, (u x - 1) ^ 2 ∂μ) + Real.pi * (∑' j, (r j - s j) ^ 2) ≤ 0 := by
  have hpoly : (fun x ↦ (u x - 1) ^ 2) =
      (fun x ↦ (u x ^ 2 - 2 * u x) + 1) := by
    funext x
    ring
  have hsub : Integrable (fun x ↦ u x ^ 2 - 2 * u x) μ := hu2.sub (hu.const_mul 2)
  rw [hpoly, integral_add hsub (integrable_const 1),
    integral_sub hu2 (hu.const_mul 2), integral_const_mul,
    (hasSum_square_discrepancy hr hs).tsum_eq]
  nlinarith

theorem equality_of_estimates {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {u : X → ℝ} {r s : ι → ℝ} {A : ℝ}
    (hu : Integrable u μ) (hu2 : Integrable (fun x ↦ u x ^ 2) μ)
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _, (1 : ℝ) ∂μ) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ x, u x ^ 2 ∂μ) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ x, u x ∂μ) + 2 * Real.pi * (∑' j, r j * s j)) :
    (u =ᵐ[μ] fun _ ↦ 1) ∧ (∀ j, r j = s j) := by
  have hd := discrepancy_nonpos hu hu2 hr hs hsource htarget hflux
  have hi : 0 ≤ ∫ x, (u x - 1) ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have ht : 0 ≤ ∑' j, (r j - s j) ^ 2 := tsum_nonneg fun j ↦ sq_nonneg _
  have hp : 0 ≤ Real.pi * (∑' j, (r j - s j) ^ 2) := mul_nonneg Real.pi_pos.le ht
  have hiz : (∫ x, (u x - 1) ^ 2 ∂μ) = 0 := by linarith
  have htz : (∑' j, (r j - s j) ^ 2) = 0 := by nlinarith [Real.pi_pos]
  have hint : Integrable (fun x ↦ (u x - 1) ^ 2) μ := by
    convert! (hu2.sub (hu.const_mul 2)).add (integrable_const 1) using 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  constructor
  · have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (u x - 1)) hint).mp hiz
    filter_upwards [hae] with x hx
    have h : u x - 1 = 0 := sq_eq_zero_iff.mp hx
    linarith
  · intro j
    have hle := (hasSum_square_discrepancy hr hs).summable.le_tsum j
      (fun k _ ↦ sq_nonneg (r k - s k))
    rw [htz] at hle
    nlinarith [sq_nonneg (r j - s j)]

theorem norm_deriv_eq_one_of_ae {f : ℂ → ℂ} {D W : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hW : IsOpen W) (hWD : W ⊆ D)
    (hae : (fun z ↦ ‖deriv f z‖) =ᵐ[volume.restrict W] fun _ ↦ 1) :
    ∀ z ∈ W, ‖deriv f z‖ = 1 :=
  Measure.eqOn_open_of_ae_eq hae hW ((hf.deriv hD).continuousOn.norm.mono hWD) continuousOn_const

theorem affine_of_unit_derivative_on_open {f : ℂ → ℂ} {D W : Set ℂ}
    (hD : IsOpen D) (hc : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hW : IsOpen W) (hne : W.Nonempty) (hWD : W ⊆ D)
    (hnorm : ∀ z ∈ W, ‖deriv f z‖ = 1) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z ∈ D, f z = a * z + b := by
  obtain ⟨z₀, hz₀⟩ := hne
  have hd : DifferentiableOn ℂ (deriv f) D := hf.deriv hD
  have hevent : (deriv f) =ᶠ[𝓝 z₀] fun _ ↦ deriv f z₀ := by
    apply Complex.eventually_eq_of_isLocalMax_norm
    · exact hd.eventually_differentiableAt (hD.mem_nhds (hWD hz₀))
    · filter_upwards [hW.mem_nhds hz₀] with z hz
      change ‖deriv f z‖ ≤ ‖deriv f z₀‖
      rw [hnorm z hz, hnorm z₀ hz₀]
  have heq : EqOn (deriv f) (fun _ ↦ deriv f z₀) D :=
    (hd.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hc (hWD hz₀) hevent
  have hlin : Differentiable ℂ (fun z : ℂ ↦ deriv f z₀ * z) :=
    differentiable_id.const_mul _
  have heq' : EqOn (deriv f) (deriv (fun z : ℂ ↦ deriv f z₀ * z)) D := by
    intro z hz
    simpa using heq hz
  obtain ⟨b, hb⟩ := hD.exists_eq_add_of_deriv_eq hc hf hlin.differentiableOn heq'
  exact ⟨deriv f z₀, b, hnorm z₀ hz₀, hb⟩

theorem affine_coefficients_of_principal_normalization {a b : ℂ}
    (hlim : Tendsto (fun z : ℂ ↦ a * z + b - z) (cobounded ℂ) (𝓝 0)) :
    a = 1 ∧ b = 0 := by
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have hprod : Tendsto (fun z : ℂ ↦ (a * z + b - z) * z⁻¹)
      (cobounded ℂ) (𝓝 0) := by simpa using hlim.mul hinv
  have hne : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := isBounded_singleton
  have heq : (fun z : ℂ ↦ (a * z + b - z) * z⁻¹) =ᶠ[cobounded ℂ]
      (fun z ↦ (a - 1) + b * z⁻¹) := by
    filter_upwards [hne] with z hz
    simp only [sub_mul, add_mul, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    ring
  have ha_lim : Tendsto (fun z : ℂ ↦ (a - 1) + b * z⁻¹)
      (cobounded ℂ) (𝓝 (a - 1)) := by
    simpa using tendsto_const_nhds.add (hinv.const_mul b)
  have ha : a = 1 := sub_eq_zero.mp (tendsto_nhds_unique ha_lim (hprod.congr' heq))
  refine ⟨ha, ?_⟩
  have hb_lim : Tendsto (fun _ : ℂ ↦ b) (cobounded ℂ) (𝓝 0) := by
    simpa [ha] using hlim
  exact tendsto_nhds_unique tendsto_const_nhds hb_lim

theorem eq_id_of_affine_and_principal_normalization {f : ℂ → ℂ}
    {D : Set ℂ} {a b : ℂ} (hD : IsBounded Dᶜ)
    (haffine : ∀ z ∈ D, f z = a * z + b)
    (hlim : Tendsto (fun z : ℂ ↦ f z - z) (cobounded ℂ) (𝓝 0)) :
    ∀ z ∈ D, f z = z := by
  have hmem : ∀ᶠ z : ℂ in cobounded ℂ, z ∈ D := by
    simpa only [eventually_mem_set, isBounded_def, compl_compl] using hD
  have he : (fun z : ℂ ↦ f z - z) =ᶠ[cobounded ℂ] (fun z ↦ a * z + b - z) := by
    filter_upwards [hmem] with z hz
    rw [haffine z hz]
  obtain ⟨ha, hb⟩ := affine_coefficients_of_principal_normalization (hlim.congr' he)
  intro z hz
  simpa [ha, hb] using haffine z hz

theorem affine_of_length_area_estimates {ι : Type*} {f : ℂ → ℂ} {D W : Set ℂ}
    {r s : ι → ℝ} {A : ℝ}
    (hD : IsOpen D) (hc : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hW : IsOpen W) (hne : W.Nonempty) (hbW : IsBounded W) (hWD : W ⊆ D)
    (hi : Integrable (fun z ↦ ‖deriv f z‖) (volume.restrict W))
    (hi2 : Integrable (fun z ↦ ‖deriv f z‖ ^ 2) (volume.restrict W))
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _ in W, (1 : ℝ)) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ z in W, ‖deriv f z‖ ^ 2) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ z in W, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z ∈ D, f z = a * z + b) ∧ (∀ j, r j = s j) := by
  let : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.mpr hbW.measure_lt_top.ne
  obtain ⟨hae, heq⟩ := equality_of_estimates hi hi2 hr hs hsource htarget hflux
  have hnorm := norm_deriv_eq_one_of_ae hD hf hW hWD hae
  exact ⟨affine_of_unit_derivative_on_open hD hc hf hW hne hWD hnorm, heq⟩

theorem identity_of_length_area_estimates {ι : Type*} {f : ℂ → ℂ} {D W : Set ℂ}
    {r s : ι → ℝ} {A : ℝ}
    (hD : IsOpen D) (hc : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    (hDinf : IsBounded Dᶜ)
    (hlim : Tendsto (fun z : ℂ ↦ f z - z) (cobounded ℂ) (𝓝 0))
    (hW : IsOpen W) (hne : W.Nonempty) (hbW : IsBounded W) (hWD : W ⊆ D)
    (hi : Integrable (fun z ↦ ‖deriv f z‖) (volume.restrict W))
    (hi2 : Integrable (fun z ↦ ‖deriv f z‖ ^ 2) (volume.restrict W))
    (hr : Summable (fun j ↦ r j ^ 2)) (hs : Summable (fun j ↦ s j ^ 2))
    (hsource : (∫ _ in W, (1 : ℝ)) + Real.pi * (∑' j, r j ^ 2) ≤ A)
    (htarget : (∫ z in W, ‖deriv f z‖ ^ 2) + Real.pi * (∑' j, s j ^ 2) ≤ A)
    (hflux : 2 * A ≤ 2 * (∫ z in W, ‖deriv f z‖) +
      2 * Real.pi * (∑' j, r j * s j)) :
    (∀ z ∈ D, f z = z) ∧ (∀ j, r j = s j) := by
  obtain ⟨⟨a, b, _, hab⟩, heq⟩ :=
    affine_of_length_area_estimates hD hc hf hW hne hbW hWD
      hi hi2 hr hs hsource htarget hflux
  exact ⟨eq_id_of_affine_and_principal_normalization hDinf hab hlim, heq⟩

end CircleDomainRigidity.LengthArea

end

end OAI
