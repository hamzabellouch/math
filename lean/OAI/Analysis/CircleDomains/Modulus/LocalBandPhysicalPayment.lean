import OAI.Analysis.CircleDomains.Modulus.LocalBandIntervalPayment
import OAI.Analysis.CircleDomains.Modulus.WeightedPhysicalChart
import OAI.Analysis.CircleDomains.Modulus.PhysicalTagPayment

namespace OAI

/-! The singleton-contact argument gives a physical payment
inequality on every retained parameter interval. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem local_band_interval_physical_payment
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B D V Flags : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ p ∈ Gᶜ, π p ∈ B) (hBD : Bᶜ ⊆ D) (hdense : Dense D)
    (hD : IsOpen D) (hV : IsOpen V) (hinfty : π OnePoint.infty ∉ V)
    (hFlags : Flags.Countable)
    {f : Sphere → ℝ} {M : ℝ} (hM : ∀ z ∈ D, |f z| ≤ M) (hf : ContinuousOn f (D ∩ V))
    (H : UnitAddCircle → Set Sphere) (hH : ∀ θ, IsClosed (H θ))
    (hlevel : ∀ z ∈ V, ∀ θ, (z, θ) ∈ circleBandGraph D f ↔ z ∈ H θ)
    {U : Set Sphere} (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Sphere)
    (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Sphere) (hφ : Continuous φ) {A O : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAO : A ⊆ O) (hO : IsOpen O)
    (j : Sphere → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (L : ℝ≥0) (hL : LipschitzOnWith L j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {r s : PathTime} (hrs : r < s)
    (hγV : γ.val '' Icc r s ⊆ V)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v O)
    (hvf : ∀ z ∈ A, f (π (φ z)) = v z)
    (hcover : ∀ x ∈ γ.val '' Icc r s ∩ D, ∃ z ∈ A, π (φ z) = x)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags ∩ V, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    {a b c : ℝ} (ha : ∀ t, (γ.val r, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (γ.val s, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ γ.val '' Icc r s ∩ (H θ), z ∈ B \ Flags →
        ¬ (connectedComponentIn (H θ) z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ physicalTagPayment e y₀ γ
      (fun y => (L : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) y) m (Icc r s) := by
  have hp := local_band_interval_image_payment hsard hsch G π hπ hclosed hsurj hr
    hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf H hH hlevel γ.val hrs hγV m hm ha hb hbranch hfree
  have hi := quotient_smooth_interval_image_le_physical e hU y₀ π hπ he φ hφ hA hφA
    hAG hAO hO j hjm hj L hL γ hrs hv f D hvf hcover
  exact hp.trans (by
    change _ ≤ tagPaymentMeasure (physicalTimeLength e y₀ γ)
      (fun t => (L : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ v (j y)‖) (physicalValue e y₀ (γ.val t))) γ.val m (Icc r s)
    rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ measurableSet_Icc]
    exact add_le_add hi le_rfl)

end CircleDomainRigidity

end

end OAI
