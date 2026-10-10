import OAI.Analysis.CircleDomains.Modulus.RealBandPhysicalPayment

namespace OAI

/-! Null free traces inside a tag: the local variation estimate and its
finite physical-plus-visit payment measure are both constructed above. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem real_band_tag_null_trace
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f D)
    {U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Sphere) (hφ : Continuous φ) {A O : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAO : A ⊆ O) (hO : IsOpen O)
    (j : Sphere → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (L : ℝ≥0) (hL : LipschitzOnWith L j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {T : Set PathTime} (hT : IsOpen T)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v O)
    (hvf : ∀ z ∈ A, f (π (φ z)) = v z)
    (hcover : ∀ x ∈ range γ.val ∩ D ∩ V, ∃ z ∈ A, π (φ z) = x)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    (hmFree : ∀ z ∈ B \ Flags, m z = 0) (hBU : B ⊆ Uᶜ)
    (trace : Sphere → ℝ)
    (htrace : ∀ z ∈ (B \ Flags) ∩ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = trace z)
    {c : ℝ} (hbranch : ∀ z ∈ V, ∀ t,
      (z, t) ∈ intervalFiberHull (clusterGraph D f) → t ∈ Ico c (c + 1))
    (hgood : ∀ᵐ θ : UnitAddCircle ∂volume, ∀ t ∈ T,
      γ.val t ∈ B \ Flags → (γ.val t, θ) ∈ circleBandGraph D f →
      ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} (γ.val t)).Nontrivial)
    (hcost : (∫⁻ y, (L : ℝ≥0∞) * (φ '' A).indicator
      (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y ∂dyadicPhysicalOccupation e y₀ γ) +
      boundaryToll γ.val m < ∞) :
    volume ((trace ∘ γ.val) ''
      ((γ.val ⁻¹' (B \ Flags)) ∩ (T ∩ γ.val ⁻¹' V))) = 0 := by
  let g : Sphere → ℝ≥0∞ := fun y => (L : ℝ≥0∞) * (φ '' A).indicator
    (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y
  have hg : Measurable g := measurable_const.mul
    ((((measurable_fderiv ℝ v).norm.ennreal_ofReal).comp hjm).indicator hφA)
  let κ := physicalTagPayment e y₀ γ g m
  let : IsFiniteMeasure κ := physicalTagPayment_finite e hU y₀ γ g hg m hcost
  have hF : MeasurableSet (γ.val ⁻¹' (B \ Flags)) :=
    γ.val.continuous.measurable (hB.measurableSet.diff hFlags.measurableSet)
  have hκF : κ (γ.val ⁻¹' (B \ Flags)) = 0 :=
    physicalTagPayment_null_free e hU y₀ γ g m hF
      (fun t ht => hBU ht.1) (fun t ht => hmFree (γ.val t) ht)
  apply path_time_null_image_of_interval_payment κ
    (hT.inter (hV.preimage γ.val.continuous))
    (measure_mono_null inter_subset_left hκF) (trace ∘ γ.val)
  intro r hr' s hs' hrs hI
  rcases hrs.eq_or_lt with hrs | hrs
  · subst s
    simp only [comp_apply, sub_self, abs_zero, ENNReal.ofReal_zero]
    exact bot_le
  · have hp := real_band_interval_physical_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf e hU y₀ he φ hφ hA hφA
      hAG hAO hO j hjm hj L hL γ hrs
      (by
        rintro x ⟨t, ht, rfl⟩
        exact (hI ht).2)
      hv hvf
      (by
        rintro x ⟨⟨t, ht, rfl⟩, hxD⟩
        exact hcover (γ.val t) ⟨⟨mem_range_self t, hxD⟩, (hI ht).2⟩)
      m hm (htrace (γ.val r) ⟨hr'.1, hr'.2.2⟩)
      (htrace (γ.val s) ⟨hs'.1, hs'.2.2⟩) hbranch ?_
    · exact hp
    · filter_upwards [hgood] with θ hθ
      rintro z ⟨⟨t, ht, htz⟩, hz⟩ hfree
      subst z
      exact hθ t (hI ht).1 hfree hz

end CircleDomainRigidity

end

end OAI
