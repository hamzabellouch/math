import OAI.Analysis.CircleDomains.Selection.RealBandPaidValues
import OAI.Analysis.CircleDomains.Modulus.ThresholdImagePayment

namespace OAI

/-! Integrating the actual paid-threshold conclusion yields the local
variation estimate in image-measure form. Only the generic singleton
statement from the independent-level argument is used. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem real_band_path_image_payment
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
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ range γ ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal (b - a) ≤ volume (f '' (range γ ∩ D)) +
      ∑' z : ↥(range γ ∩ Flags), ENNReal.ofReal
        (limsup f (𝓝[D] z.val) - liminf f (𝓝[D] z.val)) := by
  let : Countable ↥(range γ ∩ Flags) := (hFlags.mono inter_subset_right).to_subtype
  by_cases hab : a < b
  · have hai := hbranch x (hγV ⟨0, γ.source⟩) a ((ha a).mpr rfl)
    have hbi := hbranch y (hγV ⟨1, γ.target⟩) b ((hb b).mpr rfl)
    have hsub : Ioo a b ⊆ Ioc c (c + 1) := by
      intro t ht
      exact ⟨hai.1.trans_lt ht.1, (ht.2.trans hbi.2).le⟩
    have hreal := ae_restrict_of_ae_restrict_of_subset hsub
      (ae_real_interval_of_ae_circle _ hfree c)
    have hcover : ∀ᵐ t : ℝ ∂volume.restrict (Ioo a b),
        t ∈ f '' (range γ ∩ D) ∨ ∃ z : ↥(range γ ∩ Flags),
          (z.val, t) ∈ intervalFiberHull (clusterGraph D f) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hreal] with t ht hgood
      have hti : t ∈ Ico c (c + 1) := ⟨hai.1.trans ht.1.le, ht.2.trans hbi.2⟩
      rcases real_band_paid_values hsard hsch G π hπ hclosed hsurj hr
        hB hTD hbad hBD hdense hD hV hinfty hM hf γ hγV ha hb ht.1 ht.2 hti
        hbranch hgood with hdom | ⟨z, hz, hzt⟩
      · exact Or.inl hdom
      · exact Or.inr ⟨⟨z, hz⟩, hzt⟩
    exact interval_band_payment_of_ae_cover hM (fun z : ↥(range γ ∩ Flags) => z.val)
      (fun z => by rw [hdense.closure_eq]; trivial) (f '' (range γ ∩ D)) a b hcover
  · rw [ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr (le_of_not_gt hab))]
    exact bot_le

theorem real_band_path_abs_payment
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
    {x y : Sphere} (γ : Path x y) (hγV : range γ ⊆ V)
    {a b c : ℝ} (ha : ∀ t, (x, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = a)
    (hb : ∀ t, (y, t) ∈ intervalFiberHull (clusterGraph D f) ↔ t = b)
    (hbranch : ∀ z ∈ V, ∀ t, (z, t) ∈ intervalFiberHull (clusterGraph D f) →
      t ∈ Ico c (c + 1))
    (hfree : ∀ᵐ θ : UnitAddCircle ∂volume,
      ∀ z ∈ range γ ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
        ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial) :
    ENNReal.ofReal |b - a| ≤ volume (f '' (range γ ∩ D)) +
      ∑' z : ↥(range γ ∩ Flags), ENNReal.ofReal
        (limsup f (𝓝[D] z.val) - liminf f (𝓝[D] z.val)) := by
  by_cases hab : a ≤ b
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact real_band_path_image_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf γ hγV ha hb hbranch hfree
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    rw [abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    have hγ' : range γ.symm ⊆ V := by simpa only [Path.symm_range] using hγV
    have hf' : ∀ᵐ θ : UnitAddCircle ∂volume,
        ∀ z ∈ range γ.symm ∩ {z | (z, θ) ∈ circleBandGraph D f}, z ∈ B \ Flags →
          ¬ (connectedComponentIn {z | (z, θ) ∈ circleBandGraph D f} z).Nontrivial := by
      simpa only [Path.symm_range] using hfree
    have hp := real_band_path_image_payment hsard hsch G π hπ hclosed hsurj hr
      hB hTD hbad hBD hdense hD hV hinfty hFlags hM hf γ.symm hγ' hb ha hbranch hf'
    have hset : range γ.symm ∩ Flags = range γ ∩ Flags := by rw [Path.symm_range]
    rw [hset] at hp
    simpa only [Path.symm_range] using hp

end CircleDomainRigidity

end

end OAI
