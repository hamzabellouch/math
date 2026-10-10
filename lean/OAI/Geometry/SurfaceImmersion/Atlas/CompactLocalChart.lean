import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalInjectivity
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace OAI

/-! Compatible local charts near an injectively parameterized compact
set restrict to one actual open partial homeomorphism. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [Nonempty X]

theorem compact_local_chart_with_property (R : OpenPartialHomeomorph X Y → Prop) {f : X → Y} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) (hi : K.InjOn f)
    (hloc : ∀ x ∈ K, ∃ e : OpenPartialHomeomorph X Y,
      x ∈ e.source ∧ EqOn e f e.source ∧ R e) :
    ∃ e : OpenPartialHomeomorph X Y, K ⊆ e.source ∧ (e : X → Y) = f ∧
      ∀ x ∈ e.source, ∃ d : OpenPartialHomeomorph X Y, x ∈ d.source ∧ EqOn d f d.source ∧ R d := by
  classical
  let S := {e : OpenPartialHomeomorph X Y // EqOn e f e.source ∧ R e}
  let U : Set X := ⋃ e : S, e.val.source
  have hU : IsOpen U := isOpen_iUnion fun e => e.val.open_source
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨e,hxe,he,hR⟩ := hloc x hx
    exact mem_iUnion.mpr ⟨⟨e,he,hR⟩,hxe⟩
  obtain ⟨V,hV,hKV,hVI⟩ := compact_local_injectivity hf hK hi (by
    intro x hx
    obtain ⟨e,hxe,he,hR⟩ := hloc x hx
    refine ⟨e.source,e.open_source,hxe,?_⟩
    intro y hy z hz hyz
    exact e.injOn hy hz ((he hy).trans (hyz.trans (he hz).symm)))
  let W := V ∩ U
  have hW : IsOpen W := hV.inter hU
  have hKW : K ⊆ W := subset_inter hKV hKU
  have hWI : W.InjOn f := hVI.mono inter_subset_left
  have hopen : ∀ A : Set X, IsOpen A → A ⊆ W → IsOpen (f '' A) := by
    intro A hA hAW
    have heq : f '' A = ⋃ e : S, e.val '' (A ∩ e.val.source) := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        obtain ⟨e,hxe⟩ := mem_iUnion.mp (hAW hx).2
        exact mem_iUnion.mpr ⟨e,x,⟨hx,hxe⟩,e.property.1 hxe⟩
      · intro hy
        obtain ⟨e,x,⟨hx,hxe⟩,hxy⟩ := mem_iUnion.mp hy
        exact ⟨x,hx,(e.property.1 hxe).symm.trans hxy⟩
    rw [heq]
    exact isOpen_iUnion fun e => e.val.isOpen_image_of_subset_source
      (hA.inter e.val.open_source) inter_subset_right
  let p := hWI.toPartialEquiv f W
  have hpOpen : IsOpenMap (p.source.domRestrict p) := by
    change IsOpenMap (W.domRestrict f)
    intro A hA
    have himage := hopen (Subtype.val '' A) (hW.isOpenMap_subtype_val A hA)
      (by rintro x ⟨y,hy,rfl⟩; exact y.property)
    change IsOpen ((fun x : W => f x) '' A)
    simpa only [Set.image_image] using himage
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn hpOpen hW
  refine ⟨e,hKW,rfl,?_⟩
  intro x hx
  obtain ⟨d,hxd⟩ := mem_iUnion.mp hx.2
  exact ⟨d.val,hxd,d.property⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
