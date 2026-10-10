import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveCover
import OAI.MeasureTheory.Falconer.Slicing.OrientedSlice
import OAI.MeasureTheory.Falconer.Geometry.TubeAnchorNet

namespace OAI

/-! # Bounded anchor lists for every original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h m : ℕ} {κ : Type*}

noncomputable def cappedActiveAnchors (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R t : ℝ) : Finset κ :=
  if ((gaussianActiveAnchors A z J a R).card : ℝ) ≤ t then
    gaussianActiveAnchors A z J a R else ∅

theorem cappedActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ((cappedActiveAnchors A z J a R t).card : ℝ) ≤ t := by
  unfold cappedActiveAnchors
  split_ifs with hc
  · exact hc
  · simpa only [Finset.card_empty,Nat.cast_zero] using ht

theorem cappedActiveAnchors_eq (A : Fin h → Space d) (z : Space h)
    (J : Finset κ) (a : κ → Space d) (R : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hc : (gaussianActiveAnchorCount A J a R z : ℝ≥0∞) ≤ ENNReal.ofReal t) :
    cappedActiveAnchors A z J a R t = gaussianActiveAnchors A z J a R := by
  apply ite_eq_left
  apply (ENNReal.ofReal_le_ofReal_iff ht).mp
  simpa only [ENNReal.ofReal_natCast,gaussianActiveAnchors_card] using hc

theorem gaussian_capped_coordinate_cover
    (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m)
    (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
    {δ ε D M K t : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ D)
    (hanchor : ∀ w, ∀ i ∈ J w, ‖a i‖ ≤ D)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ ε)
    {x : Space d} {w : Sphere d}
    (hx : x ∈ gaussianPointBand A z δ) (hw : w ∈ gaussianDirectionBand A δ)
    (hE : ((A,z),(x,w)) ∈ gaussianActiveRelation E J a (δ+(2*D)*δ+ε*M) (ENNReal.ofReal t) true) :
    ∃ i ∈ cappedActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) t,
      ‖perpendicularPart (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)-
          e ((gaussianRowMap A).ker.orthogonalProjectionOnto (a i)))‖ ≤ ε := by
  classical
  obtain ⟨i,hi,hperp⟩ := hcover (x,w) hE.1
  have hlength := bounded_anchor_longitudinal (w := w) (hbounded (x,w) hE.1) (hanchor w i hi)
  have hactive : i ∈ gaussianActiveAnchors A z (J w) a (δ+(2*D)*δ+ε*M) :=
    Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx hperp hlength⟩
  refine ⟨i,?_,?_⟩
  · rw [cappedActiveAnchors_eq A z (J w) a _ ht hE.2]
    exact hactive
  · exact (oriented_slice_tube_width (gaussianRowMap A).ker e hsmall
      (gaussian_direction_band_kernel_distance A hK hbound hw) x (a i)).trans hperp

end Falconer

end OAI
