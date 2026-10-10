import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveRelation
import OAI.MeasureTheory.Falconer.Slicing.GaussianTubeGeometry

namespace OAI

/-! # The projected fiber cover keeps the original direction label -/

namespace Falconer
open Set NormedSpace
open scoped ENNReal
variable {d h : ℕ} {ι : Type*}

noncomputable def gaussianActiveAnchors (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) : Finset ι := by
  classical
  exact J.filter (fun i => a i ∈ gaussianPointBand A z R)

theorem gaussianActiveAnchors_card (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (R : ℝ) :
    (gaussianActiveAnchors A z J a R).card = gaussianActiveAnchorCount A J a R z := rfl

theorem gaussian_active_fiber_cover (A : Fin h → Space d) (z : Space h)
    (J : Finset ι) (a : ι → Space d) (E : Set (Space d)) (w : Sphere d)
    {δ ε L M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hA : ∀ i, ‖A i‖ ≤ M)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*δ) < 1) (hw : w ∈ gaussianDirectionBand A δ)
    (hcover : ∀ x ∈ E, ∃ i ∈ J,
      ‖perpendicularPart (w:Space d) (x-a i)‖ ≤ ε ∧ |inner ℝ (w:Space d) (x-a i)| ≤ L) :
    ∀ x ∈ E ∩ gaussianPointBand A z δ,
      ∃ i ∈ gaussianActiveAnchors A z J a (δ+L*δ+ε*M),
        ‖perpendicularPart (normalize ((gaussianRowMap A).ker.starProjection (w:Space d)))
          ((gaussianRowMap A).ker.starProjection x-(gaussianRowMap A).ker.starProjection (a i))‖ ≤ ε := by
  classical
  intro x hx
  obtain ⟨i,hi,hperp,hlength⟩ := hcover x hx.1
  refine ⟨i,?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨hi,gaussian_active_anchor A z hM hA hw hx.2 hperp hlength⟩
  · exact (gaussian_projected_tube_width A hK hbound hsmall hw x (a i)).trans hperp

end Falconer

end OAI
