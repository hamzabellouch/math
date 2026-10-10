import OAI.MeasureTheory.Falconer.Angular.CappedActiveCover

namespace OAI

/-! # The capped slice cover still consists of original tube anchors -/

namespace Falconer
open Set
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

theorem gaussian_capped_original_cover
    (A : Fin h → Space d) (z : Space h)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset ι) (a : ι → Space d)
    {δ ε D M t : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖a i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ ε)
    {x : Space d} {w : Sphere d}
    (hx : x ∈ gaussianPointBand A z δ) (hw : w ∈ gaussianDirectionBand A δ)
    (hE : ((A,z),(x,w)) ∈ gaussianActiveRelation E J a (δ+(2*D)*δ+ε*M) (ENNReal.ofReal t) true) :
    ∃ c ∈ (cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t).image a,
      ‖perpendicularPart (w:Space d) (x-c)‖ ≤ ε := by
  classical
  obtain ⟨i,hi,hperp⟩ := hcover (x,w) hE.1
  have hlength := bounded_anchor_longitudinal (w := w) (hbounded (x,w) hE.1) (hanchor w i hi)
  have hactive : i ∈ gaussianActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) :=
    Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx hperp hlength⟩
  have hi' : i ∈ cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t := by
    rw [cappedActiveAnchors_eq A z (J w) a _ ht hE.2]
    exact hactive
  exact ⟨a i,Finset.mem_image.mpr ⟨i,hi',rfl⟩,hperp⟩

theorem capped_original_cover_card
    (A : Fin h → Space d) (z : Space h) (J : Finset ι) (a : ι → Space d)
    (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (((cappedActiveAnchors A z J a R t).image a).card:ℝ) ≤ t := by
  classical
  exact (Nat.cast_le.mpr Finset.card_image_le).trans (cappedActiveAnchors_card A z J a R ht)

end Falconer

end OAI
