import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.SmallControlCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallControlTransfer
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)

include hc hd in

theorem small_control_comparison (f g : TrackStar α →* H)
    (hf : SmallSupported L f) (hfg : SmallControlled c f g)
    (J : Finset α) (u v : H) (hu : u ∈ L J) (hv : v ∈ L J)
    (hreserve : J.card+10 ≤ Fintype.card α)
    (hact : ∀ (I : ControlAlphabet α) t,
      u*g (universalMap (subtypeAlternatingHom I.val) t)*u⁻¹ =
        v*g (universalMap (subtypeAlternatingHom I.val) t)*v⁻¹) :
    ∀ x ∈ f.range, u*x*u⁻¹ = v*x*v⁻¹ := by
  have hh := small_control_transfer L c hc hd f g hf hfg J (u⁻¹*v)
    ((L J).mul_mem ((L J).inv_mem hu) hv) hreserve
    (fun I t => (same_conj_iff _ _ _).mp (hact I t))
  intro x hx
  exact (same_conj_iff _ _ _).mpr (hh x hx)

include hc hd in

theorem small_control_trans (hα : 20 ≤ Fintype.card α)
    (hconst : SmallSupported L (c.comp (universalProjection (alternatingGroup α))))
    (f g k : TrackStar α →* H) (hf : SmallSupported L f) (hk : SmallSupported L k)
    (hfg : SmallControlled c f g) (hgk : SmallControlled c g k) :
    SmallControlled c f k := by
  intro I t x hx
  apply small_control_comparison L c hc hd f g hf hfg I.val
    (k (universalMap (subtypeAlternatingHom I.val) t))
    (c (universalProjection (alternatingGroup α) (universalMap (subtypeAlternatingHom I.val) t)))
    (hk I ⟨t,rfl⟩) (hconst I ⟨t,rfl⟩) (by have hh := I.property.2; omega) ?_ x hx
  intro J s
  exact hgk I t _ ⟨universalMap (subtypeAlternatingHom J.val) s,rfl⟩

include hc hd in

theorem small_control_disjoint (hα : 20 ≤ Fintype.card α)
    (f g j k : TrackStar α →* H)
    (hf : SmallSupported L f) (hg : SmallSupported L g) (hj : SmallSupported L j)
    (hfj : SmallControlled c f j) (hgk : SmallControlled c g k)
    (hjk : ∀ s t, Commute (j s) (k t)) : ∀ s t, Commute (f s) (g t) := by
  have hjg (I : ControlAlphabet α) (s : UniversalExtension (alternatingGroup I.val)) :
      ∀ x ∈ g.range, Commute (j (universalMap (subtypeAlternatingHom I.val) s)) x :=
    small_control_transfer L c hc hd g k hg hgk I.val _ (hj I ⟨s,rfl⟩)
      (by have hh := I.property.2; omega) (fun J t => hjk _ _)
  have hfg (I : ControlAlphabet α) (t : UniversalExtension (alternatingGroup I.val)) :
      ∀ x ∈ f.range, Commute (g (universalMap (subtypeAlternatingHom I.val) t)) x :=
    small_control_transfer L c hc hd f j hf hfj I.val _ (hg I ⟨t,rfl⟩)
      (by have hh := I.property.2; omega)
      (fun J s => (hjg J s _ ⟨universalMap (subtypeAlternatingHom I.val) t,rfl⟩).symm)
  intro s
  let C := Subgroup.centralizer ({f s} : Set H)
  have hC : g.range ≤ C := by
    rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate (by omega : 5 ≤ Fintype.card α),
      Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [← MonoidHom.range_comp]
    rintro x ⟨t,rfl⟩ y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    let J : ControlAlphabet α := ⟨I.val,by have hh := I.property.2; omega,
      by have hh := I.property.2; omega⟩
    exact (hfg J t _ ⟨s,rfl⟩).eq.symm
  intro t
  exact hC ⟨t,rfl⟩ (f s) (Set.mem_singleton _)

theorem small_control_intersection (f a b d e : TrackStar α →* H)
    (hbd : ∀ s t, Commute (b s) (d t))
    (hbe : ∀ s t, Commute (b s) (e t))
    (hde : ∀ s t, Commute (d s) (e t))
    (hwhole : ∀ s, c (universalProjection (alternatingGroup α) s) = a s*b s*d s*e s)
    (hJ : ∀ I : ControlAlphabet α,
      SameActionOn (fun t => a (universalMap (subtypeAlternatingHom I.val) t)*
        b (universalMap (subtypeAlternatingHom I.val) t))
      ((c.comp (universalProjection (alternatingGroup α))).comp
        (universalMap (subtypeAlternatingHom I.val))) f.range)
    (hK : ∀ I : ControlAlphabet α,
      SameActionOn (fun t => a (universalMap (subtypeAlternatingHom I.val) t)*
        d (universalMap (subtypeAlternatingHom I.val) t))
      ((c.comp (universalProjection (alternatingGroup α))).comp
        (universalMap (subtypeAlternatingHom I.val))) f.range) :
    SmallControlled c f a := by
  intro I
  exact intersection_control
    (a.comp (universalMap (subtypeAlternatingHom I.val)))
    (b.comp (universalMap (subtypeAlternatingHom I.val)))
    (d.comp (universalMap (subtypeAlternatingHom I.val)))
    (e.comp (universalMap (subtypeAlternatingHom I.val)))
    ((c.comp (universalProjection (alternatingGroup α))).comp
      (universalMap (subtypeAlternatingHom I.val))) f.range
    (fun s t => hbd _ _) (fun s t => hbe _ _) (fun s t => hde _ _)
    (fun s => hwhole _) (hJ I) (hK I)

end SmallControlTransfer

end SimpleAmenable
end
end

end OAI
