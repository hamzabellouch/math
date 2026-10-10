import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionAnodyneHorn
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.KanFiberComponentTransport

namespace OAI

section

/-! # The carrier of a realized ordered homotopy

An ordered simplicial prism chooses an endpoint image at every vertex.
Its realized support is therefore contained in the union of the two
endpoint supports at the original parameter point.
-/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Convexity RealizationPrism
open scoped Simplicial

noncomputable section

theorem homotopy_support_of_vertex_choices {K : SSet.{0}} {P : Type} [PartialOrder P]
    {f g : K ⟶ nerve P} (H : SSet.Homotopy f g)
    (hv : ∀ (n : ℕ) (s : (K ⊗ Δ[1]) _⦋n⦌) (i : Fin (n+1)),
      (H.h.app _ s).obj i = (f.app _ s.1).obj i ∨
      (H.h.app _ s).obj i = (g.app _ s.1).obj i)
    (t : unitInterval) (z : SSet.toTop.obj K) (y : P)
    (hy : (coordinates P (RealizedCylinder.homotopy H (t, z))).weights y ≠ 0) :
    (coordinates P ((SSet.toTop.map f).hom z)).weights y ≠ 0 ∨
      (coordinates P ((SSet.toTop.map g).hom z)).weights y ≠ 0 := by
  classical
  obtain ⟨n, s, p, hs⟩ := point_representation_simplex (K ⊗ Δ[1])
    ((RealizedCylinder.comparison K).hom (z, t))
  have hz : simplexPoint K s.1 p = z := by
    calc
      _ = (SSet.toTop.map (fst K Δ[1])).hom
          (simplexPoint (K ⊗ Δ[1]) s p) :=
        (simplexPoint_naturality (fst K Δ[1]) s p).symm
      _ = _ := (congrArg (SSet.toTop.map (fst K Δ[1])).hom hs).trans
        (RealizedCylinder.comparison_first K z t)
  have hh : coordinates P (RealizedCylinder.homotopy H (t, z)) =
      StdSimplex.map (H.h.app _ s).obj p := by
    rw [realizedHomotopy_apply, ← hs, simplexPoint_naturality,
      coordinates_simplexPoint]
  have hf : coordinates P ((SSet.toTop.map f).hom z) =
      StdSimplex.map (f.app _ s.1).obj p := by
    rw [← hz, simplexPoint_naturality, coordinates_simplexPoint]
  have hg : coordinates P ((SSet.toTop.map g).hom z) =
      StdSimplex.map (g.app _ s.1).obj p := by
    rw [← hz, simplexPoint_naturality, coordinates_simplexPoint]
  rw [hh] at hy
  have hys : y ∈ (p.weights.mapDomain (H.h.app _ s).obj).support :=
    Finsupp.mem_support_iff.mpr hy
  rw [Finsupp.support_mapDomain_of_nonneg p.nonneg] at hys
  obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hys
  rcases hv n s i with h | h
  · left
    rw [hf]
    apply Finsupp.mem_support_iff.mp
    change y ∈ (p.weights.mapDomain (f.app _ s.1).obj).support
    rw [Finsupp.support_mapDomain_of_nonneg p.nonneg]
    exact Finset.mem_image.mpr ⟨i, hi, h.symm.trans hiy⟩
  · right
    rw [hg]
    apply Finsupp.mem_support_iff.mp
    change y ∈ (p.weights.mapDomain (g.app _ s.1).obj).support
    rw [Finsupp.support_mapDomain_of_nonneg p.nonneg]
    exact Finset.mem_image.mpr ⟨i, hi, h.symm.trans hiy⟩

theorem orderedVertexHomotopy_support {K : SSet.{0}} {P : Type} [PartialOrder P]
    (f g : K ⟶ nerve P)
    (hfg : ∀ v : K _⦋0⦌, (f.app _ v).obj 0 ≤ (g.app _ v).obj 0)
    (t : unitInterval) (z : SSet.toTop.obj K) (y : P)
    (hy : (coordinates P
      (RealizedCylinder.homotopy (orderedVertexHomotopy f g hfg) (t, z))).weights y ≠ 0) :
    (coordinates P ((SSet.toTop.map f).hom z)).weights y ≠ 0 ∨
      (coordinates P ((SSet.toTop.map g).hom z)).weights y ≠ 0 := by
  apply homotopy_support_of_vertex_choices (orderedVertexHomotopy f g hfg) _ t z y hy
  intro n s i
  change (if (SSet.stdSimplex.objEquiv s.2).toOrderHom i = 0 then
    (f.app _ s.1).obj i else (g.app _ s.1).obj i) = (f.app _ s.1).obj i ∨
    (if (SSet.stdSimplex.objEquiv s.2).toOrderHom i = 0 then
    (f.app _ s.1).obj i else (g.app _ s.1).obj i) = (g.app _ s.1).obj i
  split_ifs <;> simp

theorem orderNerveHomotopy_support {Q P : Type} [PartialOrder Q] [PartialOrder P]
    (f g : Q →o P) (hfg : ∀ q, f q ≤ g q)
    (t : unitInterval) (z : SSet.toTop.obj (nerve Q)) (y : P)
    (hy : (coordinates P
      (RealizedCylinder.homotopy (orderNerveHomotopy f g hfg) (t, z))).weights y ≠ 0) :
    (coordinates P ((SSet.toTop.map (nerveMap f.monotone.functor)).hom z)).weights y ≠ 0 ∨
      (coordinates P ((SSet.toTop.map (nerveMap g.monotone.functor)).hom z)).weights y ≠ 0 := by
  apply homotopy_support_of_vertex_choices (orderNerveHomotopy f g hfg) _ t z y hy
  intro n s i
  change (if (SSet.stdSimplex.objEquiv s.2).toOrderHom i = 0 then
    f (s.1.obj i) else g (s.1.obj i)) = f (s.1.obj i) ∨
    (if (SSet.stdSimplex.objEquiv s.2).toOrderHom i = 0 then
    f (s.1.obj i) else g (s.1.obj i)) = g (s.1.obj i)
  split_ifs <;> simp

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Naturality of the ordered-vertex prism -/

namespace Thomason.Construction.PosetGeometry

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

theorem orderedVertexHomotopy_naturality
    {K L : SSet.{0}} {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f₀ f₁ : K ⟶ nerve P) (g₀ g₁ : L ⟶ nerve Q)
    (hf : ∀ v : K _⦋0⦌, (f₀.app _ v).obj 0 ≤ (f₁.app _ v).obj 0)
    (hg : ∀ v : L _⦋0⦌, (g₀.app _ v).obj 0 ≤ (g₁.app _ v).obj 0)
    (u : K ⟶ L) (v : P →o Q)
    (h₀ : u ≫ g₀ = f₀ ≫ nerveMap v.monotone.functor)
    (h₁ : u ≫ g₁ = f₁ ≫ nerveMap v.monotone.functor) :
    (u ▷ Δ[1]) ≫ (orderedVertexHomotopy g₀ g₁ hg).h =
      (orderedVertexHomotopy f₀ f₁ hf).h ≫ nerveMap v.monotone.functor := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply nerve.ext_of_isThin
  funext i
  change (if (SSet.stdSimplex.objEquiv t).toOrderHom i = 0 then
      (g₀.app n (u.app n s)).obj i else (g₁.app n (u.app n s)).obj i) =
    v (if (SSet.stdSimplex.objEquiv t).toOrderHom i = 0 then
      (f₀.app n s).obj i else (f₁.app n s).obj i)
  split_ifs
  · exact congrArg (fun q => (q.app n s).obj i) h₀
  · exact congrArg (fun q => (q.app n s).obj i) h₁

end

end Thomason.Construction.PosetGeometry

end

section

/-! # Whiskering and exact extension invariance under simplicial homotopies -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Pre- and postcompose an actual simplicial homotopy. -/
def whiskerSimplicialHomotopy {A X Y B : SSet.{0}} (a : A ⟶ X) {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (b : Y ⟶ B) :
    SSet.Homotopy (a ≫ f ≫ b) (a ≫ g ≫ b) where
  h := a ▷ Δ[1] ≫ H.h ≫ b
  h₀ := by
    have hn : SSet.ι₀ ≫ a ▷ (Δ[1] : SSet.{0}) = a ≫ SSet.ι₀ := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, ← Category.assoc SSet.ι₀, H.h₀]
    rfl
  h₁ := by
    have hn : SSet.ι₁ ≫ a ▷ (Δ[1] : SSet.{0}) = a ≫ SSet.ι₁ := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, ← Category.assoc SSet.ι₁, H.h₁]
    rfl
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- Kan cylinder lifting works also when the prescribed total-space map
is the final endpoint. It makes a boundary homotopy exact at its start. -/
theorem kan_extension_of_boundary_homotopy_reverse {A K X : SSet.{0}}
    [SSet.KanComplex X] (i : A ⟶ K) [Mono i] (a : A ⟶ X) (d : K ⟶ X)
    (H : SSet.Homotopy a (i ≫ d)) :
    ∃ l : K ⟶ X, i ≫ l = a := by
  obtain ⟨e, _, hei, _⟩ := exists_kan_cylinder_lift_one i (terminal.from X)
    d H.h (terminal.from _) H.h₁ (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  refine ⟨SSet.ι₀ ≫ e, ?_⟩
  have hn : i ≫ SSet.ι₀ = SSet.ι₀ ≫ i ▷ (Δ[1] : SSet.{0}) := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  rw [← Category.assoc, hn, Category.assoc, hei, H.h₀]

/-- Solvability of an exact extension problem in a Kan target is unchanged
by an actual simplicial homotopy of its prescribed boundary map. -/
theorem kan_extension_iff_of_boundary_homotopy {A K X : SSet.{0}}
    [SSet.KanComplex X] (i : A ⟶ K) [Mono i] {a b : A ⟶ X}
    (H : SSet.Homotopy a b) :
    (∃ d : K ⟶ X, i ≫ d = a) ↔ (∃ d : K ⟶ X, i ≫ d = b) := by
  constructor
  · rintro ⟨d, hd⟩
    have H' : SSet.Homotopy (i ≫ d) b := by rw [hd]; exact H
    obtain ⟨l, hl, _⟩ := kan_lift_of_boundary_homotopy i (terminal.from X)
      d (terminal.from _) (terminal.hom_ext _ _) b H' (terminal.hom_ext _ _)
    exact ⟨l, hl⟩
  · rintro ⟨d, hd⟩
    have H' : SSet.Homotopy a (i ≫ d) := by rw [hd]; exact H
    exact kan_extension_of_boundary_homotopy_reverse i a d H'

/-- A map with a simplicial homotopy left inverse preserves and reflects
all exact monomorphic extension problems in a Kan source. -/
theorem kan_extension_iff_of_homotopy_left_inverse {A K X Y : SSet.{0}}
    [SSet.KanComplex X] (i : A ⟶ K) [Mono i] (a : A ⟶ X)
    (f : X ⟶ Y) (g : Y ⟶ X) (H : SSet.Homotopy (𝟙 X) (f ≫ g)) :
    (∃ d : K ⟶ X, i ≫ d = a) ↔ (∃ d : K ⟶ Y, i ≫ d = a ≫ f) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d ≫ f, by rw [← Category.assoc, hd]⟩
  · rintro ⟨d, hd⟩
    have HA : SSet.Homotopy a (a ≫ f ≫ g) := by
      simpa only [Category.id_comp, Category.comp_id] using
        whiskerSimplicialHomotopy a H (𝟙 X)
    apply (kan_extension_iff_of_boundary_homotopy i HA).mpr
    exact ⟨d ≫ g, by rw [← Category.assoc, hd, Category.assoc]⟩

end

end Thomason.Construction

end

end OAI
