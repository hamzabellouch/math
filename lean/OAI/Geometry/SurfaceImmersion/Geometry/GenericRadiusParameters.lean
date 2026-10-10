import OAI.Geometry.SurfaceImmersion.Geometry.CompactRegularParameters
import OAI.Geometry.SurfaceImmersion.Geometry.LowerDimensionalImage

namespace OAI

/-! Simultaneous independent radius selection. Pair projections avoid
critical values and triple projections avoid surface images in three
coordinates, within every allowed open parameter box. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι κ : Type*} [Countable ι] [Countable κ]

theorem exists_generic_radius_parameters
    (pair : ι → E →L[ℝ] Plane) (hpair : ∀ i, Function.Surjective (pair i))
    (triple : κ → E →L[ℝ] (Plane × ℝ)) (htriple : ∀ j, Function.Surjective (triple j))
    (f : ι → Plane → Plane) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (g : κ → Plane → Plane × ℝ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (L : κ → Set Plane) (hL : ∀ j, IsCompact (L j))
    (U : Set E) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ t ∈ U,
      (∀ i x, x ∈ K i → f i x = pair i t → Function.Surjective (fderiv ℝ (f i) x)) ∧
      (∀ i, (K i ∩ {x | f i x = pair i t}).Finite) ∧
      ∀ j x, x ∈ L j → g j x ≠ triple j t := by
  let O : Sum ι κ → Set E
    | .inl i => (pair i) ⁻¹' compactRegularValues (f i) (K i)
    | .inr j => (triple j) ⁻¹' (g j '' L j)ᶜ
  have ho : ∀ a, IsOpen (O a) := by
    intro a
    cases a with
    | inl i =>
        exact (compact_regular_values_open_dense (f i) (hf i) (hK i)).1.preimage
          (pair i).continuous
    | inr j =>
        exact (compact_surface_image_open_dense (g j) (hg j) (hL j)).1.preimage
          (triple j).continuous
  have hd : ∀ a, Dense (O a) := by
    intro a
    cases a with
    | inl i =>
        exact (compact_regular_values_open_dense (f i) (hf i) (hK i)).2.preimage
          ((pair i).isOpenMap (hpair i))
    | inr j =>
        exact (compact_surface_image_open_dense (g j) (hg j) (hL j)).2.preimage
          ((triple j).isOpenMap (htriple j))
  obtain ⟨t,htU,ht⟩ := (dense_iInter_of_isOpen ho hd).inter_open_nonempty U hU hne
  have hreg (i : ι) : ∀ x ∈ K i, f i x = pair i t →
      Function.Surjective (fderiv ℝ (f i) x) := mem_iInter.mp ht (Sum.inl i)
  refine ⟨t,htU,hreg,fun i => finite_compact_regular_fiber (hf i) (hK i) _ (hreg i),?_⟩
  intro j x hx he
  have hn : triple j t ∉ g j '' L j := mem_iInter.mp ht (Sum.inr j)
  exact hn ⟨x,hx,he⟩

end ClosedSurfaceR4.PublishedInputs

end

end OAI
