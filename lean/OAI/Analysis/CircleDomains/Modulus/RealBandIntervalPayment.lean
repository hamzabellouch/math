import OAI.Analysis.CircleDomains.Modulus.RealBandPathPayment
import OAI.Analysis.CircleDomains.Probability.TagPaymentMeasure
import OAI.Analysis.CircleDomains.Topology.IntervalPath

namespace OAI

/-! Absolute variation on an actual parameter interval, paid by domain
image length and the atomic measure of flagged visits. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem real_band_interval_image_payment
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
    (γ : C(PathTime, Sphere)) {r s : PathTime} (hrs : r < s)
    (hγV : γ '' Icc r s ⊆ V)
    (m : Sphere → ℝ≥0∞)
    (hm : ∀ z ∈ Flags, ENNReal.ofReal
      (limsup f (𝓝[D] z) - liminf f (𝓝[D] z)) ≤ m z)
    {a b c : ℝ} (ha : ∀ t, (γ r, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (γ s, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ γ '' Icc r s ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ volume (f '' (γ '' Icc r s ∩ D)) + boundaryTimeMeasure γ m (Icc r s) := by
  let α := intervalPath γ r s
  have hrange : range α = γ '' Icc r s := intervalPath_range γ hrs
  have hp := real_band_path_abs_payment hsard hsch G π hπ hclosed hsurj hr
    hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf α
    (by simpa only [hrange] using hγV) ha hb hbranch
    (by simpa only [hrange] using hfree)
  have hset : range α ∩ Flags = γ '' Icc r s ∩ Flags := by rw [hrange]
  rw [hset, hrange] at hp
  apply hp.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑' z : ↥(γ '' Icc r s ∩ Flags), m z.val :=
      ENNReal.tsum_le_tsum (fun z => hm z.val z.property.2)
    _ ≤ _ := boundaryTimeMeasure_image_le γ m measurableSet_Icc inter_subset_left

end CircleDomainRigidity

end

end OAI
