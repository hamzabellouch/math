import OAI.CategoryTheory.Thomason.Gray.SimplicialHomotopyWhiskering
import OAI.CategoryTheory.Thomason.Gray.SingularCylinderEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.FixedInternalPathMaps
import OAI.CategoryTheory.Thomason.Simplicial.KanContractedFamilyLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanFiberComponentTransport
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology
import OAI.CategoryTheory.Thomason.Simplicial.TruncationCongruence
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.Order.NonemptyFiniteChains

namespace OAI

section

/-! # Exact cubical boundary extensions and simplicial nullhomotopies -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- Restrict the simultaneous cube contraction through a given extension.
This is a homotopy of the whole cubical boundary, with both endpoints exact. -/
def boundaryNullhomotopyOfExtension {X : SSet.{0}} (n : ℕ)
    (a : (boundary n : SSet.{0}) ⟶ X) (d : obj (n+1) ⟶ X)
    (hd : (boundary n).ι ≫ d = a) :
    SSet.Homotopy (SSet.const (d.app _ (initialVertex (n+1)))) a := by
  have H := whiskerSimplicialHomotopy (boundary n).ι (initialContraction (n+1)) d
  simpa only [SSet.comp_const, SSet.const_comp, Category.id_comp, hd] using H

/-- The whole cubical boundary has an exact extension in a Kan complex
if and only if its given map has an actual simplicial nullhomotopy. -/
theorem kan_boundary_extension_iff_nullhomotopy {X : SSet.{0}} [SSet.KanComplex X]
    (n : ℕ) (a : (boundary n : SSet.{0}) ⟶ X) :
    (∃ d : obj (n+1) ⟶ X, (boundary n).ι ≫ d = a) ↔
      ∃ x : X _⦋0⦌, Nonempty (SSet.Homotopy (SSet.const x) a) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d.app _ (initialVertex (n+1)), ⟨boundaryNullhomotopyOfExtension n a d hd⟩⟩
  · rintro ⟨x, ⟨H⟩⟩
    exact Thomason.Construction.kan_extension_of_nullhomotopy (boundary n).ι a x H

end

end Thomason.Construction.RealizedCube

end

section

/-! # Exact finite singular carriers for realized homotopies -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory
open scoped Simplicial

noncomputable section

/-- A continuous homotopy between realized simplicial maps gives an actual
simplicial homotopy after the realization/singular unit. Its evaluation is
exact; no weak-equivalence assertion about that unit is used. -/
def realizationUnitHomotopy {A X : SSet.{0}} {f g : A ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    SSet.Homotopy (f ≫ sSetTopAdj.unit.app X) (g ≫ sSetTopAdj.unit.app X) where
  h := sSetTopAdj.unit.app A ▷ Δ[1] ≫ (singularHomotopy H).h
  h₀ := by
    have hn : SSet.ι₀ ≫ sSetTopAdj.unit.app A ▷ (Δ[1] : SSet.{0}) =
        sSetTopAdj.unit.app A ≫ SSet.ι₀ := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, (singularHomotopy H).h₀]
    exact (sSetTopAdj.unit.naturality f).symm
  h₁ := by
    have hn : SSet.ι₁ ≫ sSetTopAdj.unit.app A ▷ (Δ[1] : SSet.{0}) =
        sSetTopAdj.unit.app A ≫ SSet.ι₁ := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    rw [← Category.assoc, hn, Category.assoc, (singularHomotopy H).h₁]
    exact (sSetTopAdj.unit.naturality g).symm
  rel := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- The singular carrier retains the complete original continuous homotopy. -/
theorem realizationUnitHomotopy_evaluate {A X : SSet.{0}} {f g : A ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom)
    (t : unitInterval) (x : SSet.toTop.obj A) :
    evaluateSingularCylinder (realizationUnitHomotopy H).h (t, x) = H (t, x) :=
  evaluateSingularCylinder_unit H t x

/-- For a finite parameter complex, the entire continuous homotopy gives
one finite singular subcomplex, with both original endpoint maps retained
exactly after the unit. It does not assert an approximation in `X` itself. -/
theorem finite_singular_homotopy_support {A X : SSet.{0}} [A.Finite] {f g : A ⟶ X}
    (H : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map g).hom) :
    ∃ S : (TopCat.toSSet.obj (SSet.toTop.obj X)).Subcomplex,
      SSet.Finite S.toSSet ∧ ∃ (fS gS : A ⟶ S.toSSet) (HS : SSet.Homotopy fS gS),
        fS ≫ S.ι = f ≫ sSetTopAdj.unit.app X ∧
        gS ≫ S.ι = g ≫ sSetTopAdj.unit.app X ∧
        HS.h ≫ S.ι = (realizationUnitHomotopy H).h := by
  let h := realizationUnitHomotopy H
  let S := SSet.Subcomplex.range h.h
  let q := SSet.Subcomplex.toRange h.h
  let fS := SSet.ι₀ ≫ q
  let gS := SSet.ι₁ ≫ q
  let HS : SSet.Homotopy fS gS := {
    h := q
    h₀ := rfl
    h₁ := rfl
    rel := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }
  refine ⟨S, inferInstance, fS, gS, HS, ?_, ?_, rfl⟩
  · change (SSet.ι₀ ≫ q) ≫ S.ι = _
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, h.h₀]
  · change (SSet.ι₁ ≫ q) ≫ S.ι = _
    rw [Category.assoc, SSet.Subcomplex.toRange_ι, h.h₁]

end

end Thomason.Construction

end

section

/-! # Finite exact singular nullhomotopies for higher boundary approximation -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- A continuous nullhomotopy of a finite simplicial family has an exact
simplicial nullhomotopy in one finite subcomplex of the singular realization.
The given family is retained after the unit. Moving this witness into `X`
itself requires approximation. -/
theorem finite_singular_nullhomotopy_support {A X : SSet.{0}} [A.Finite]
    (v : A _⦋0⦌) (x : X _⦋0⦌) (a : A ⟶ X)
    (H : (ContinuousMap.const (SSet.toTop.obj A) (RealizationPrism.vertexPoint X x)).Homotopy
      (SSet.toTop.map a).hom) :
    ∃ S : (TopCat.toSSet.obj (SSet.toTop.obj X)).Subcomplex,
      SSet.Finite S.toSSet ∧ ∃ (xS : S.toSSet _⦋0⦌) (aS : A ⟶ S.toSSet),
        aS ≫ S.ι = a ≫ sSetTopAdj.unit.app X ∧
        Nonempty (SSet.Homotopy (SSet.const xS) aS) := by
  have hc : (SSet.toTop.map (SSet.const (X := A) x)).hom =
      ContinuousMap.const (SSet.toTop.obj A) (RealizationPrism.vertexPoint X x) := by
    apply ContinuousMap.ext
    exact RealizationPrism.realization_const x
  have H' : (SSet.toTop.map (SSet.const (X := A) x)).hom.Homotopy
      (SSet.toTop.map a).hom := H.cast hc.symm rfl
  obtain ⟨S, hS, fS, aS, HS, hf, ha, _⟩ := finite_singular_homotopy_support H'
  let xS := fS.app _ v
  have hconst : (SSet.const (X := A) xS) ≫ S.ι =
      (SSet.const (X := A) x) ≫ sSetTopAdj.unit.app X := by
    calc
      (SSet.const (X := A) xS) ≫ S.ι = (SSet.const v ≫ fS) ≫ S.ι := by
        simp only [SSet.const_comp]
        rfl
      _ = SSet.const v ≫ ((SSet.const (X := A) x) ≫ sSetTopAdj.unit.app X) := by
        rw [Category.assoc, hf]
      _ = (SSet.const (X := A) x) ≫ sSetTopAdj.unit.app X := by
        rw [← Category.assoc, SSet.comp_const]
  have hfx : fS = SSet.const xS := (cancel_mono S.ι).mp (hf.trans hconst.symm)
  rw [hfx] at HS
  exact ⟨S, hS, xS, aS, ha, ⟨HS⟩⟩

end

end Thomason.Construction

end

section

/-! # Exact lifting over a contracted base reduces to its actual fibre -/

namespace Thomason.Construction

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- For every monomorphic relative lifting problem over an explicitly
contracted base, extension of the transported boundary inside its actual
simplicial fibre is equivalent to an exact lift in the original total space.
The same chosen retraction is a strict retraction on that fibre. -/
theorem kan_lift_iff_contracted_fiber_extension {A K E B : SSet.{0}}
    (v : B _⦋0⦌) (C : SSet.Homotopy (SSet.const v) (𝟙 B))
    (hC : ∀ L : SSet.{0}, (SSet.const (X := L) v) ▷ Δ[1] ≫ C.h =
      fst L Δ[1] ≫ SSet.const v)
    (p : E ⟶ B) [HomotopicalAlgebra.Fibration p]
    (i : A ⟶ K) [Mono i] (a : A ⟶ E) (b : K ⟶ B) (hab : a ≫ p = i ≫ b) :
    ∃ r : E ⟶ (simplicialPointFiber p v).toSSet,
      (simplicialPointFiber p v).ι ≫ r = 𝟙 _ ∧
      ((∃ d : K ⟶ E, i ≫ d = a ∧ d ≫ p = b) ↔
        ∃ u : K ⟶ (simplicialPointFiber p v).toSSet, i ≫ u = a ≫ r) := by
  let F := simplicialPointFiber p v
  have hs : (F.ι ≫ p) ▷ Δ[1] ≫ C.h = fst F.toSSet Δ[1] ≫ F.ι ≫ p := by
    rw [simplicialPointFiber_ι_comp]
    exact hC _
  obtain ⟨r, hr, T, _, hT⟩ := kan_fiber_deformation_reverse p v C hs
  refine ⟨r, hr, ?_⟩
  constructor
  · rintro ⟨d, hd, _⟩
    exact ⟨d ≫ r, by rw [← Category.assoc, hd]⟩
  · rintro ⟨u, hu⟩
    let d : K ⟶ E := u ≫ F.ι
    let HA := whiskerSimplicialHomotopy a T (𝟙 E)
    let HB := whiskerSimplicialHomotopy b C (𝟙 B)
    have hzero : SSet.ι₀ ≫ HA.h = i ≫ d := by
      rw [HA.h₀]
      dsimp only [d]
      simpa only [Category.comp_id, Category.assoc] using
        congrArg (fun k => k ≫ F.ι) hu.symm
    have hp : HA.h ≫ p = i ▷ Δ[1] ≫ HB.h := by
      change (a ▷ Δ[1] ≫ T.h ≫ 𝟙 E) ≫ p =
        i ▷ Δ[1] ≫ (b ▷ Δ[1] ≫ C.h ≫ 𝟙 B)
      simp only [Category.comp_id]
      rw [Category.assoc, hT, ← comp_whiskerRight_assoc, hab, comp_whiskerRight_assoc]
    have hd : d ≫ p = SSet.ι₀ ≫ HB.h := by
      rw [HB.h₀]
      dsimp only [d]
      rw [Category.comp_id, Category.assoc, simplicialPointFiber_ι_comp,
        SSet.comp_const, SSet.comp_const]
    obtain ⟨h, _, hh, hp⟩ := exists_kan_cylinder_lift i p d HA.h HB.h hzero hp hd
    refine ⟨SSet.ι₁ ≫ h, ?_, ?_⟩
    · have hn : i ≫ SSet.ι₁ = SSet.ι₁ ≫ i ▷ (Δ[1] : SSet.{0}) := by
        apply NatTrans.ext
        funext k
        apply ConcreteCategory.hom_ext
        intro x
        rfl
      rw [← Category.assoc, hn, Category.assoc, hh, HA.h₁]
      simp only [Category.comp_id]
    · rw [Category.assoc, hp, HB.h₁]
      simp only [Category.comp_id]

end

end Thomason.Construction

end

section

/-! # Higher cubical lifting as an exact simplicial fibre nullhomotopy -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- An arbitrary cubical boundary square over a finite cube lifts exactly
if and only if its transported boundary has a simplicial nullhomotopy in
the initial Kan fibre. All maps in the square and its boundary are retained. -/
theorem boundary_lift_iff_fiber_nullhomotopy {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ obj m) [HomotopicalAlgebra.Fibration p]
    (a : (boundary n : SSet.{0}) ⟶ E) (b : obj (n+1) ⟶ obj m)
    (hab : a ≫ p = (boundary n).ι ≫ b) :
    ∃ r : E ⟶ (simplicialPointFiber p (initialVertex m)).toSSet,
      (simplicialPointFiber p (initialVertex m)).ι ≫ r = 𝟙 _ ∧
      ((∃ d : obj (n+1) ⟶ E, (boundary n).ι ≫ d = a ∧ d ≫ p = b) ↔
        ∃ x, Nonempty (SSet.Homotopy (SSet.const x) (a ≫ r))) := by
  obtain ⟨r, hr, he⟩ := kan_lift_iff_contracted_fiber_extension (initialVertex m)
    (initialContraction m) (initialContraction_stationary m) p (boundary n).ι a b hab
  have : SSet.KanComplex (simplicialPointFiber p (initialVertex m)).toSSet :=
    simplicialPointFiber_kan p _
  exact ⟨r, hr, he.trans (kan_boundary_extension_iff_nullhomotopy n (a ≫ r))⟩

end

end Thomason.Construction.RealizedCube

end

section

/-! # Higher exact boundary problems are invariant under Kan interval transport -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- The two endpoint fibres of a Kan fibration over the interval have
actual simplicial homotopy inverse maps. Both maps are realization weak
equivalences, without any acyclic-Kan-lifting hypothesis. -/
theorem kan_endpoint_fibers_homotopy_inverse {E : SSet.{0}}
    (p : E ⟶ (Δ[1] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    ∃ (f : (simplicialPointFiber p (initialSimplexVertex 1)).toSSet ⟶
          (simplicialPointFiber p (finalSimplexVertex 1)).toSSet)
      (g : (simplicialPointFiber p (finalSimplexVertex 1)).toSSet ⟶
          (simplicialPointFiber p (initialSimplexVertex 1)).toSSet),
      realizationWeakEquivalences f ∧ realizationWeakEquivalences g ∧
      Nonempty (SSet.Homotopy (𝟙 _) (f ≫ g)) ∧
      Nonempty (SSet.Homotopy (g ≫ f) (𝟙 _)) := by
  let F₀ := simplicialPointFiber p (initialSimplexVertex 1)
  let F₁ := simplicialPointFiber p (finalSimplexVertex 1)
  have hs : (F₀.ι ≫ p) ▷ Δ[1] ≫ (simplexInitialContraction 1).h =
      fst F₀.toSSet Δ[1] ≫ F₀.ι ≫ p := by
    rw [simplicialPointFiber_ι_comp]
    exact simplexInitialContraction_const 1 _
  obtain ⟨r₀, hr₀, T₀, _, _⟩ :=
    kan_fiber_deformation_reverse p (initialSimplexVertex 1) (simplexInitialContraction 1) hs
  obtain ⟨r₁, hr₁, T₁, _, _⟩ := kan_simplex_fiber_deformation 1 p
  let f : F₀.toSSet ⟶ F₁.toSSet := F₀.ι ≫ r₁
  let g : F₁.toSSet ⟶ F₀.toSSet := F₁.ι ≫ r₀
  have h₀ : SSet.Homotopy (𝟙 F₀.toSSet) (f ≫ g) := by
    have h := whiskerSimplicialHomotopy F₀.ι T₁ r₀
    simpa only [F₀, F₁, f, g, Category.id_comp, Category.assoc, hr₀] using h
  have h₁ : SSet.Homotopy (g ≫ f) (𝟙 F₁.toSSet) := by
    have h := whiskerSimplicialHomotopy F₁.ι T₀ r₁
    simpa only [F₀, F₁, f, g, Category.id_comp, Category.assoc, hr₁] using h
  have hw₀ : realizationWeakEquivalences r₀ := by
    apply realizationWeakEquivalences.of_postcomp r₀ F₀.ι (kan_simplex_initialFiber_weak 1 p)
    exact (RealizedCylinder.weakEquivalence_iff T₀).mpr (realizationWeakEquivalences.id_mem _)
  have hw₁ : realizationWeakEquivalences r₁ := by
    apply realizationWeakEquivalences.of_postcomp r₁ F₁.ι (kan_simplex_fiber_weak 1 p)
    exact (RealizedCylinder.weakEquivalence_iff T₁).mp (realizationWeakEquivalences.id_mem _)
  exact ⟨f, g,
    realizationWeakEquivalences.comp_mem _ _ (kan_simplex_initialFiber_weak 1 p) hw₁,
    realizationWeakEquivalences.comp_mem _ _ (kan_simplex_fiber_weak 1 p) hw₀, ⟨h₀⟩, ⟨h₁⟩⟩

/-- A single weak simplicial transport map simultaneously preserves and
reflects exact extension problems for every monomorphism, hence all
higher boundaries. This assertion is stronger than transporting W-status. -/
theorem kan_endpoint_fibers_exact_extension {E : SSet.{0}}
    (p : E ⟶ (Δ[1] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    ∃ f : (simplicialPointFiber p (initialSimplexVertex 1)).toSSet ⟶
        (simplicialPointFiber p (finalSimplexVertex 1)).toSSet,
      realizationWeakEquivalences f ∧
      ∀ (A K : SSet.{0}) (i : A ⟶ K) (_ : Mono i)
        (a : A ⟶ (simplicialPointFiber p (initialSimplexVertex 1)).toSSet),
        (∃ d : K ⟶ (simplicialPointFiber p (initialSimplexVertex 1)).toSSet, i ≫ d = a) ↔
          (∃ d : K ⟶ (simplicialPointFiber p (finalSimplexVertex 1)).toSSet, i ≫ d = a ≫ f) := by
  obtain ⟨f, g, hf, _, ⟨H⟩, _⟩ := kan_endpoint_fibers_homotopy_inverse p
  have : SSet.KanComplex (simplicialPointFiber p (initialSimplexVertex 1)).toSSet :=
    simplicialPointFiber_kan p _
  exact ⟨f, hf, fun A K i hi a => @kan_extension_iff_of_homotopy_left_inverse
    A K _ _ inferInstance i hi a f g H⟩

end

end Thomason.Construction

end

section

/-! # Exact higher extension is invariant along realized base paths -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- Pullback identifies transport along any base interval with the actual
endpoint homotopy equivalence. No contractibility of the ambient base is required. -/
theorem kan_interval_fibers_homotopy_inverse {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (g : (Δ[1] : SSet.{0}) ⟶ B) :
    ∃ (f : (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet ⟶
          (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).toSSet)
      (r : (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).toSSet ⟶
          (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet),
      realizationWeakEquivalences f ∧ realizationWeakEquivalences r ∧
      Nonempty (SSet.Homotopy (𝟙 _) (f ≫ r)) ∧
      Nonempty (SSet.Homotopy (r ≫ f) (𝟙 _)) := by
  let q := pullback.snd p g
  have : HomotopicalAlgebra.Fibration q := kan_pullback_snd_fibration p g
  let e₀ := simplicialPointFiberBaseChangeIso p g (initialSimplexVertex 1)
  let e₁ := simplicialPointFiberBaseChangeIso p g (finalSimplexVertex 1)
  obtain ⟨f, r, hf, hr, ⟨H₀⟩, ⟨H₁⟩⟩ := kan_endpoint_fibers_homotopy_inverse q
  let f' := e₀.hom ≫ f ≫ e₁.inv
  let r' := e₁.hom ≫ r ≫ e₀.inv
  have H₀' : SSet.Homotopy (𝟙 _) (f' ≫ r') := by
    have H := whiskerSimplicialHomotopy e₀.hom H₀ e₀.inv
    convert H using 1 <;> simp [f', r', Category.assoc]
    change _ = e₀.hom ≫ (𝟙 _) ≫ e₀.inv
    rw [Category.id_comp, e₀.hom_inv_id]
  have H₁' : SSet.Homotopy (r' ≫ f') (𝟙 _) := by
    have H := whiskerSimplicialHomotopy e₁.hom H₁ e₁.inv
    convert H using 1 <;> simp [f', r', Category.assoc]
    change _ = e₁.hom ≫ (𝟙 _) ≫ e₁.inv
    rw [Category.id_comp, e₁.hom_inv_id]
  exact ⟨f', r',
    realizationWeakEquivalences.comp_mem _ _ (realizationWeakEquivalences.of_isIso _)
      (realizationWeakEquivalences.comp_mem _ _ hf (realizationWeakEquivalences.of_isIso _)),
    realizationWeakEquivalences.comp_mem _ _ (realizationWeakEquivalences.of_isIso _)
      (realizationWeakEquivalences.comp_mem _ _ hr (realizationWeakEquivalences.of_isIso _)),
    ⟨H₀'⟩, ⟨H₁'⟩⟩

/-- In every degree, exact boundary extension in the fibre is invariant
along an arbitrary base interval. Both implications produce exact fillers. -/
theorem kan_fiber_boundary_extension_iff_of_interval {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] (g : (Δ[1] : SSet.{0}) ⟶ B) (n : ℕ) :
    (∀ a : (SSet.boundary n : SSet.{0}) ⟶
        (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ _, (SSet.boundary n).ι ≫ d = a) ↔
    (∀ a : (SSet.boundary n : SSet.{0}) ⟶
        (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ _, (SSet.boundary n).ι ≫ d = a) := by
  obtain ⟨f, r, _, _, ⟨H₀⟩, ⟨H₁⟩⟩ := kan_interval_fibers_homotopy_inverse p g
  have : SSet.KanComplex
      (simplicialPointFiber p (g.app _ (initialSimplexVertex 1))).toSSet :=
    simplicialPointFiber_kan p _
  have : SSet.KanComplex
      (simplicialPointFiber p (g.app _ (finalSimplexVertex 1))).toSSet :=
    simplicialPointFiber_kan p _
  constructor
  · intro h a
    obtain ⟨d, hd⟩ := h (a ≫ r)
    have H := whiskerSimplicialHomotopy a H₁ (𝟙 _)
    have H' : SSet.Homotopy ((a ≫ r) ≫ f) a := by
      simpa only [Category.assoc, Category.comp_id] using H
    obtain ⟨l, hl⟩ := (kan_extension_iff_of_boundary_homotopy (SSet.boundary n).ι H').mp
      ⟨d ≫ f, by rw [← Category.assoc, hd]⟩
    exact ⟨l, hl⟩
  · intro h a
    have hx := (kan_extension_iff_of_homotopy_left_inverse
      (SSet.boundary n).ι a f r H₀).mpr (h (a ≫ f))
    exact hx

/-- Exact higher fibre extensions are constant on a simplicial edge. -/
theorem kan_fiber_boundary_extension_iff_of_edge {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌} (e : SSet.Edge x y) (n : ℕ) :
    (∀ a : (SSet.boundary n : SSet.{0}) ⟶ (simplicialPointFiber p x).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ _, (SSet.boundary n).ι ≫ d = a) ↔
    (∀ a : (SSet.boundary n : SSet.{0}) ⟶ (simplicialPointFiber p y).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ _, (SSet.boundary n).ι ≫ d = a) := by
  let g : (Δ[1] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm e.edge
  have hi : g.app _ (initialSimplexVertex 1) = x := by
    dsimp only [g, initialSimplexVertex]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    have hv : RealizationPrism.vertexOperator (0 : Fin 2) = SimplexCategory.δ (1 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl
    rw [hv]
    exact e.src_eq
  have ht : g.app _ (finalSimplexVertex 1) = y := by
    dsimp only [g, finalSimplexVertex]
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    have hv : RealizationPrism.vertexOperator (Fin.last 1) = SimplexCategory.δ (0 : Fin 2) := by
      apply SimplexCategory.Hom.ext
      apply DFunLike.ext
      intro j
      fin_cases j
      rfl
    rw [hv]
    exact e.tgt_eq
  have h := kan_fiber_boundary_extension_iff_of_interval p g n
  rw [hi, ht] at h
  exact h

/-- A continuous path between realized base vertices transports every
higher exact fibre extension test. Only the proved component comparison
is used to pass to a finite edge zigzag. -/
theorem kan_fiber_boundary_extension_iff_of_realization_path {E B : SSet.{0}} (p : E ⟶ B)
    [HomotopicalAlgebra.Fibration p] {x y : B _⦋0⦌}
    (h : Path (RealizationPrism.vertexPoint B x) (RealizationPrism.vertexPoint B y)) (n : ℕ) :
    (∀ a : (SSet.boundary n : SSet.{0}) ⟶ (simplicialPointFiber p x).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ _, (SSet.boundary n).ι ≫ d = a) ↔
    (∀ a : (SSet.boundary n : SSet.{0}) ⟶ (simplicialPointFiber p y).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ _, (SSet.boundary n).ι ≫ d = a) := by
  have hz := RealizationPrism.edge_zigzag_of_realization_path h
  clear h
  induction hz with
  | rel a b h => exact kan_fiber_boundary_extension_iff_of_edge p (Classical.choice h) n
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end

end Thomason.Construction

end

section

/-! # Higher lifting over a simplex reduces to exact extension in one fibre -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen
open scoped Simplicial

noncomputable section

/-- For a Kan fibration over a standard simplex, a prescribed boundary
lifts exactly whenever all boundaries of that degree extend in the initial
vertex fibre. The proof transports the whole boundary along the stationary
base contraction, extends in the fibre, and lifts the return cylinder. -/
theorem simplex_boundary_lifting_of_initial_fiber {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ (Δ[m] : SSet.{0})) [HomotopicalAlgebra.Fibration p]
    (hF : ∀ a : (SSet.boundary n : SSet.{0}) ⟶
        (simplicialPointFiber p (initialSimplexVertex m)).toSSet,
      ∃ d : (Δ[n] : SSet.{0}) ⟶ (simplicialPointFiber p (initialSimplexVertex m)).toSSet,
        (SSet.boundary n).ι ≫ d = a) :
    HasLiftingProperty (SSet.boundary n).ι p := by
  let F := simplicialPointFiber p (initialSimplexVertex m)
  have hs : (F.ι ≫ p) ▷ Δ[1] ≫ (simplexInitialContraction m).h =
      fst F.toSSet Δ[1] ≫ F.ι ≫ p := by
    rw [simplicialPointFiber_ι_comp]
    exact simplexInitialContraction_const m _
  obtain ⟨r, _, T, _, hT⟩ :=
    kan_fiber_deformation_reverse p _ (simplexInitialContraction m) hs
  refine ⟨fun {a b} sq => ?_⟩
  obtain ⟨dF, hdF⟩ := hF (a ≫ r)
  let d : (Δ[n] : SSet.{0}) ⟶ E := dF ≫ F.ι
  let HA := whiskerSimplicialHomotopy a T (𝟙 E)
  let HB := whiskerSimplicialHomotopy b (simplexInitialContraction m) (𝟙 _)
  have hzero : SSet.ι₀ ≫ HA.h = (SSet.boundary n).ι ≫ d := by
    rw [HA.h₀]
    dsimp only [d]
    simpa only [Category.comp_id, Category.assoc] using
      congrArg (fun k => k ≫ F.ι) hdF.symm
  have hp : HA.h ≫ p = (SSet.boundary n).ι ▷ Δ[1] ≫ HB.h := by
    change (a ▷ Δ[1] ≫ T.h ≫ 𝟙 E) ≫ p =
      (SSet.boundary n).ι ▷ Δ[1] ≫ (b ▷ Δ[1] ≫ (simplexInitialContraction m).h ≫ 𝟙 _)
    simp only [Category.comp_id]
    rw [Category.assoc, hT, ← comp_whiskerRight_assoc, sq.w, comp_whiskerRight_assoc]
  have hd : d ≫ p = SSet.ι₀ ≫ HB.h := by
    rw [HB.h₀]
    dsimp only [d]
    rw [Category.comp_id, Category.assoc, simplicialPointFiber_ι_comp,
      SSet.comp_const, SSet.comp_const]
  obtain ⟨h, _, hh, hp⟩ := exists_kan_cylinder_lift (SSet.boundary n).ι p d HA.h HB.h
    hzero hp hd
  refine ⟨⟨{ l := SSet.ι₁ ≫ h, fac_left := ?_, fac_right := ?_ }⟩⟩
  · have hn : (SSet.boundary n).ι ≫ SSet.ι₁ =
        SSet.ι₁ ≫ (SSet.boundary n).ι ▷ (Δ[1] : SSet.{0}) := by
      apply NatTrans.ext
      funext k
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, hh, HA.h₁]
    simp only [Category.comp_id]
  · rw [Category.assoc, hp, HB.h₁]
    simp only [Category.comp_id]

/-- The exact converse: boundary lifting against the fibration restricts
to boundary extension in its literal initial fibre. -/
theorem initial_fiber_extension_of_simplex_boundary_lifting {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ (Δ[m] : SSet.{0}))
    (hp : HasLiftingProperty (SSet.boundary n).ι p)
    (a : (SSet.boundary n : SSet.{0}) ⟶
      (simplicialPointFiber p (initialSimplexVertex m)).toSSet) :
    ∃ d : (Δ[n] : SSet.{0}) ⟶ (simplicialPointFiber p (initialSimplexVertex m)).toSSet,
      (SSet.boundary n).ι ≫ d = a := by
  let F := simplicialPointFiber p (initialSimplexVertex m)
  let b : (Δ[n] : SSet.{0}) ⟶ Δ[m] := SSet.const (initialSimplexVertex m)
  let sq : CommSq (a ≫ F.ι) (SSet.boundary n).ι p b := ⟨by
    rw [Category.assoc, simplicialPointFiber_ι_comp, SSet.comp_const]
    exact (SSet.comp_const _ _).symm⟩
  let : HasLiftingProperty (SSet.boundary n).ι p := hp
  let d := simplicialPointFiberLift p (initialSimplexVertex m) sq.lift sq.fac_right
  refine ⟨d, ?_⟩
  apply (cancel_mono F.ι).mp
  rw [Category.assoc, simplicialPointFiberLift_ι, sq.fac_left]

/-- For every degree, lifting over a standard simplex is precisely the
extension problem in its initial Kan fibre. -/
theorem simplex_boundary_lifting_iff_initial_fiber {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ (Δ[m] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    HasLiftingProperty (SSet.boundary n).ι p ↔
      ∀ a : (SSet.boundary n : SSet.{0}) ⟶
          (simplicialPointFiber p (initialSimplexVertex m)).toSSet,
        ∃ d : (Δ[n] : SSet.{0}) ⟶ (simplicialPointFiber p (initialSimplexVertex m)).toSSet,
          (SSet.boundary n).ι ≫ d = a :=
  ⟨fun hp a => initial_fiber_extension_of_simplex_boundary_lifting m n p hp a,
    simplex_boundary_lifting_of_initial_fiber m n p⟩

/-- The remaining local higher lifting step is EXACTLY a simplicial
nullhomotopy in the initial fibre. No continuous approximation is assumed. -/
theorem simplex_boundary_lifting_iff_fiber_nullhomotopies {E : SSet.{0}} (m n : ℕ)
    (p : E ⟶ (Δ[m] : SSet.{0})) [HomotopicalAlgebra.Fibration p] :
    HasLiftingProperty (SSet.boundary n).ι p ↔
      ∀ a : (SSet.boundary n : SSet.{0}) ⟶
          (simplicialPointFiber p (initialSimplexVertex m)).toSSet,
        ∃ x, Nonempty (SSet.Homotopy (SSet.const x) a) := by
  have : SSet.KanComplex (simplicialPointFiber p (initialSimplexVertex m)).toSSet :=
    simplicialPointFiber_kan p _
  rw [simplex_boundary_lifting_iff_initial_fiber m n p]
  exact forall_congr' (fun a => kan_boundary_extension_iff_nullhomotopy n a)

end

end Thomason.Construction

end

section

/-! # The face-poset collapse underlying a subdivided horn

Delete the omitted facet first. The remaining face-poset pair admits the
explicit zigzag `id ≤ (A ↦ A ∪ {k}) ≥ (A ↦ {k})`, with the full face fixed
by the second map. It reduces the horn pair to a vertex in an interval.
-/

namespace Thomason.Construction.SubdivisionHornFaces

open CategoryTheory MonoidalCategory CartesianMonoidalCategory PartialOrder
open scoped Simplicial

noncomputable section

abbrev Faces (n : ℕ) := NonemptyFiniteChains (ULift.{0} (Fin (n + 2)))

def omitted (n : ℕ) (k : Fin (n + 2)) : Finset (ULift.{0} (Fin (n + 2))) :=
  Finset.univ.erase (ULift.up k)

abbrev Remainder (n : ℕ) (k : Fin (n + 2)) :=
  {A : Faces n // A.finset ≠ omitted n k}

abbrev HornFaces (n : ℕ) (k : Fin (n + 2)) :=
  {A : Remainder n k // A.val.finset ≠ Finset.univ}

instance (n : ℕ) (k : Fin (n + 2)) : PartialOrder (Remainder n k) :=
  inferInstanceAs (PartialOrder {A : Faces n // A.finset ≠ omitted n k})

instance (n : ℕ) (k : Fin (n + 2)) : PartialOrder (HornFaces n k) :=
  inferInstanceAs (PartialOrder {A : Remainder n k // A.val.finset ≠ Finset.univ})

def topFace (n : ℕ) : Faces n where
  finset := Finset.univ
  comparable a b := le_total a.val b.val

def vertexFace (n : ℕ) (k : Fin (n + 2)) : Faces n where
  finset := {ULift.up k}
  comparable a b := le_total a.val b.val

theorem vertex_ne_top (n : ℕ) (k : Fin (n + 2)) :
    (vertexFace n k).finset ≠ Finset.univ := by
  intro h
  have hc := congrArg Finset.card h
  simp [vertexFace] at hc

def vertex (n : ℕ) (k : Fin (n + 2)) : HornFaces n k :=
  ⟨⟨vertexFace n k, by
    intro h
    have hm : ULift.up k ∈ omitted n k := h ▸ (by simp [vertexFace])
    simp [omitted] at hm⟩, vertex_ne_top n k⟩

def top (n : ℕ) (k : Fin (n + 2)) : Remainder n k :=
  ⟨topFace n, by
    intro h
    have hm : ULift.up k ∈ omitted n k := h ▸ (by simp [topFace])
    simp [omitted] at hm⟩

def inclusion (n : ℕ) (k : Fin (n + 2)) : HornFaces n k →o Remainder n k :=
  ⟨Subtype.val, fun _ _ h => h⟩

def addVertex (n : ℕ) (k : Fin (n + 2)) : Remainder n k →o Remainder n k where
  toFun A := ⟨{
      finset := insert (ULift.up k) A.val.finset
      nonempty := Finset.insert_nonempty _ _
      comparable a b := le_total a.val b.val }, by
    intro h
    have hm : ULift.up k ∈ omitted n k := h ▸ (Finset.mem_insert_self _ _)
    simp [omitted] at hm⟩
  monotone' _ _ h := Finset.insert_subset_insert _ h

theorem addVertex_proper (n : ℕ) (k : Fin (n + 2)) (A : HornFaces n k) :
    ((addVertex n k) A.val).val.finset ≠ Finset.univ := by
  intro h
  change insert (ULift.up k) A.val.val.finset = Finset.univ at h
  by_cases hk : ULift.up k ∈ A.val.val.finset
  · rw [Finset.insert_eq_of_mem hk] at h
    exact A.property h
  · have he := congrArg (fun s => s.erase (ULift.up k)) h
    rw [Finset.erase_insert hk] at he
    exact A.val.property he

def addVertexHorn (n : ℕ) (k : Fin (n + 2)) : HornFaces n k →o HornFaces n k where
  toFun A := ⟨addVertex n k A.val, addVertex_proper n k A⟩
  monotone' _ _ h := (addVertex n k).monotone h

def rank (n : ℕ) (k : Fin (n + 2)) : Remainder n k →o Fin 2 where
  toFun A := if A.val.finset = Finset.univ then 1 else 0
  monotone' A B h := by
    by_cases hA : A.val.finset = Finset.univ
    · have hB : B.val.finset = Finset.univ :=
        Finset.univ_subset_iff.mp (hA ▸ h)
      simp only [hA, hB, ↓reduceIte, le_refl]
    · simp only [hA, ↓reduceIte]
      exact Fin.zero_le _

def edgeSection (n : ℕ) (k : Fin (n + 2)) : Fin 2 →o Remainder n k where
  toFun t := if t = 0 then (vertex n k).val else top n k
  monotone' a b hab := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · simp only [ha, hb, ↓reduceIte, le_refl]
      · simp only [ha, hb, ↓reduceIte]
        exact Finset.subset_univ _
    · have hb : b ≠ 0 := by omega
      simp only [ha, hb, ↓reduceIte, le_refl]

def toPoint (n : ℕ) (k : Fin (n + 2)) : HornFaces n k →o Unit :=
  OrderHom.const _ ()

def fromPoint (n : ℕ) (k : Fin (n + 2)) : Unit →o HornFaces n k :=
  OrderHom.const _ (vertex n k)

def intervalStart : Unit →o Fin 2 := OrderHom.const _ 0

theorem identity_le_addVertex (n : ℕ) (k : Fin (n + 2)) (A : Remainder n k) :
    A ≤ addVertex n k A := Finset.subset_insert _ _

theorem section_rank_le_addVertex (n : ℕ) (k : Fin (n + 2)) (A : Remainder n k) :
    edgeSection n k (rank n k A) ≤ addVertex n k A := by
  change (if (if A.val.finset = Finset.univ then (1 : Fin 2) else 0) = 0
    then (vertex n k).val else top n k) ≤ addVertex n k A
  by_cases hA : A.val.finset = Finset.univ
  · simp only [hA, ↓reduceIte, one_ne_zero]
    change Finset.univ ⊆ insert (ULift.up k) A.val.finset
    rw [hA]
    exact Finset.subset_insert _ _
  · simp only [hA, ↓reduceIte]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)

theorem identity_le_addVertexHorn (n : ℕ) (k : Fin (n + 2)) (A : HornFaces n k) :
    A ≤ addVertexHorn n k A := identity_le_addVertex n k A.val

theorem point_le_addVertexHorn (n : ℕ) (k : Fin (n + 2)) (A : HornFaces n k) :
    fromPoint n k (toPoint n k A) ≤ addVertexHorn n k A :=
  Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)

theorem nerveMap_mono {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) (hf : Function.Injective f) : Mono (nerveMap f.monotone.functor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro a b hab
  apply nerve.ext_of_isThin
  funext t
  apply hf
  exact congrArg (fun s => s.obj t) hab

theorem intervalStart_anodyne : SSet.anodyneExtensions (nerveMap intervalStart.monotone.functor) := by
  let j := nerveMap intervalStart.monotone.functor
  have : Mono j := nerveMap_mono intervalStart (fun _ _ _ => Subsingleton.elim _ _)
  let r := nerveMap (OrderHom.const (Fin 2) ()).monotone.functor
  have hjr : j ≫ r = 𝟙 _ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext t
    exact Subsingleton.elim _ _
  let H := PosetGeometry.orderedVertexHomotopy (r ≫ j) (𝟙 (nerve (Fin 2)))
    (fun x => Fin.zero_le (x.obj 0))
  apply anodyne_of_simplicial_deformation j r hjr H
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply nerve.ext_of_isThin
  funext q
  change (if (SSet.stdSimplex.objEquiv t).toOrderHom q = 0 then 0 else 0) = 0
  split <;> rfl

/-- After removal of the omitted facet, the full horn face-poset inclusion
is anodyne. The proof is the two explicit ordered homotopies of the pair. -/
theorem hornFaces_inclusion_anodyne (n : ℕ) (k : Fin (n + 2)) :
    SSet.anodyneExtensions (nerveMap (inclusion n k).monotone.functor) := by
  let i := nerveMap (inclusion n k).monotone.functor
  let j := nerveMap intervalStart.monotone.functor
  let rA := nerveMap (toPoint n k).monotone.functor
  let rB := nerveMap (rank n k).monotone.functor
  let sA := nerveMap (fromPoint n k).monotone.functor
  let sB := nerveMap (edgeSection n k).monotone.functor
  let uA := nerveMap (addVertexHorn n k).monotone.functor
  let uB := nerveMap (addVertex n k).monotone.functor
  have : Mono i := nerveMap_mono (inclusion n k) Subtype.val_injective
  have hr : i ≫ rB = rA ≫ j := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext q
    change (if (x.obj q).val.val.finset = Finset.univ then 1 else 0) = 0
    simp only [(x.obj q).property, ↓reduceIte]
  have hs : j ≫ sB = sA ≫ i := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext q
    rfl
  have hu : i ≫ uB = uA ≫ i := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext q
    rfl
  let HA := PosetGeometry.orderedVertexHomotopy (rA ≫ sA) uA
    (fun x => point_le_addVertexHorn n k (x.obj 0))
  let HB := PosetGeometry.orderedVertexHomotopy (rB ≫ sB) uB
    (fun x => section_rank_le_addVertex n k (x.obj 0))
  let GA := PosetGeometry.orderedVertexHomotopy (𝟙 (nerve (HornFaces n k))) uA
    (fun x => identity_le_addVertexHorn n k (x.obj 0))
  let GB := PosetGeometry.orderedVertexHomotopy (𝟙 (nerve (Remainder n k))) uB
    (fun x => identity_le_addVertex n k (x.obj 0))
  have he : i ≫ (rB ≫ sB) = (rA ≫ sA) ≫ i := by
    rw [← Category.assoc, hr, Category.assoc, hs, ← Category.assoc]
  have hH : i ▷ Δ[1] ≫ HB.h = HA.h ≫ i :=
    PosetGeometry.orderedVertexHomotopy_naturality _ _ _ _ _ _ i (inclusion n k) he hu
  have hG : i ▷ Δ[1] ≫ GB.h = GA.h ≫ i :=
    PosetGeometry.orderedVertexHomotopy_naturality _ _ _ _ _ _ i (inclusion n k)
      (by simp only [Category.comp_id, Category.id_comp]; rfl) hu
  exact anodyne_of_arrow_homotopy_zigzag i j intervalStart_anodyne
    rA rB sA sB hr hs uA uB HA HB hH GA GB hG

theorem omitted_subset_cases (n : ℕ) (k : Fin (n + 2))
    (s : Finset (ULift.{0} (Fin (n + 2)))) (h : omitted n k ⊆ s) :
    s = omitted n k ∨ s = Finset.univ := by
  by_cases hk : ULift.up k ∈ s
  · right
    apply Finset.eq_univ_iff_forall.mpr
    intro a
    by_cases ha : a = ULift.up k
    · exact ha ▸ hk
    · exact h (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩)
  · left
    apply Finset.Subset.antisymm _ h
    intro a ha
    apply Finset.mem_erase.mpr
    exact ⟨fun he => hk (he ▸ ha), Finset.mem_univ _⟩

def remainderInclusion (n : ℕ) (k : Fin (n + 2)) : Remainder n k →o Faces n :=
  ⟨Subtype.val, fun _ _ h => h⟩

def removeOmitted (n : ℕ) (k : Fin (n + 2)) : Faces n →o Remainder n k where
  toFun A := if h : A.finset = omitted n k then top n k else ⟨A, h⟩
  monotone' A B h := by
    by_cases hA : A.finset = omitted n k
    · have hcases := omitted_subset_cases n k B.finset (hA ▸ h)
      rcases hcases with hB | hB
      · simp only [hA, hB, ↓reduceDIte, le_refl]
      · have hBn : B.finset ≠ omitted n k := by
          rw [hB]
          exact (top n k).property
        simp only [hA, hBn, ↓reduceDIte]
        change Finset.univ ⊆ B.finset
        rw [hB]
    · by_cases hB : B.finset = omitted n k
      · simp only [hA, hB, ↓reduceDIte]
        exact Finset.subset_univ _
      · simp only [hA, hB, ↓reduceDIte]
        exact h

theorem removeOmitted_inclusion (n : ℕ) (k : Fin (n + 2)) (A : Remainder n k) :
    removeOmitted n k (remainderInclusion n k A) = A := by
  change (if h : A.val.finset = omitted n k then top n k else ⟨A.val, h⟩) = A
  simp only [A.property, ↓reduceDIte]

theorem identity_le_removeOmitted (n : ℕ) (k : Fin (n + 2)) (A : Faces n) :
    A ≤ remainderInclusion n k (removeOmitted n k A) := by
  change A ≤ (if h : A.finset = omitted n k then top n k else ⟨A, h⟩).val
  by_cases h : A.finset = omitted n k
  · rw [dite_eq_left h]
    exact Finset.subset_univ _
  · rw [dite_eq_right h]

/-- The omitted facet is an up-beat vertex of the full face poset. Removing
it induces an anodyne nerve inclusion by a stationary ordered homotopy. -/
theorem remainder_inclusion_anodyne (n : ℕ) (k : Fin (n + 2)) :
    SSet.anodyneExtensions (nerveMap (remainderInclusion n k).monotone.functor) := by
  let i := nerveMap (remainderInclusion n k).monotone.functor
  let r := nerveMap (removeOmitted n k).monotone.functor
  have : Mono i := nerveMap_mono (remainderInclusion n k) Subtype.val_injective
  have hir : i ≫ r = 𝟙 _ := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext q
    exact removeOmitted_inclusion n k (x.obj q)
  let HA := PosetGeometry.orderedVertexHomotopy (𝟙 (nerve (Remainder n k)))
    (𝟙 (nerve (Remainder n k))) (fun _ => le_rfl)
  let HB := PosetGeometry.orderedVertexHomotopy (𝟙 (nerve (Faces n))) (r ≫ i)
    (fun x => identity_le_removeOmitted n k (x.obj 0))
  have hH : i ▷ Δ[1] ≫ HB.h = HA.h ≫ i :=
    PosetGeometry.orderedVertexHomotopy_naturality _ _ _ _ _ _ i (remainderInclusion n k)
      (by simp only [Category.comp_id, Category.id_comp]; rfl)
      (by rw [← Category.assoc, hir, Category.id_comp])
  exact anodyne_of_arrow_homotopies_reverse i (𝟙 _) (SSet.anodyneExtensions.of_isIso _)
    (𝟙 _) r (𝟙 _) i (by simpa only [Category.comp_id] using hir)
      (by simp) (by simpa using HA) HB hH

/-- The actual inclusion of the full horn face poset in the full simplex
face poset is anodyne, in every positive dimension and for every horn. -/
theorem full_hornFaces_inclusion_anodyne (n : ℕ) (k : Fin (n + 2)) :
    SSet.anodyneExtensions (nerveMap
      ((remainderInclusion n k).comp (inclusion n k)).monotone.functor) := by
  rw [orderNerveMap_comp]
  exact SSet.anodyneExtensions.comp_mem _ _
    (hornFaces_inclusion_anodyne n k) (remainder_inclusion_anodyne n k)

end

end Thomason.Construction.SubdivisionHornFaces

end

section

/-! # Weak equivalences are surjective on path homotopy classes with fixed ends -/

namespace Thomason.Construction

open CategoryTheory

noncomputable section

/-- Surjectivity on the actual first homotopy group implies surjectivity of
Mathlib's fundamental-group map under the explicit comparison. -/
theorem fundamentalGroup_map_surjective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X)
    (hf : Function.Surjective (HomotopyMaps.groupMap f 1 x)) :
    Function.Surjective (FundamentalGroup.map f x) := by
  intro q
  obtain ⟨a, ha⟩ := hf (HomotopyGroup.pi1EquivFundamentalGroup.symm q)
  refine ⟨HomotopyGroup.pi1EquivFundamentalGroup a, ?_⟩
  rw [← HomotopyMaps.piOneEquiv_naturality, ha, Equiv.apply_symm_apply]

/-- A weak homotopy equivalence lifts any path up to homotopy relative to
its specified endpoints. This uses only component injectivity and π₁ surjectivity. -/
theorem weak_path_homotopy_surjective {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (hf : IsWeakHomotopyEquivalence f)
    {x₀ x₁ : X} (γ : Path (f x₀) (f x₁)) :
    ∃ α : Path x₀ x₁, (α.map f.continuous).Homotopic γ := by
  have he : ZerothHomotopy.mk x₀ = ZerothHomotopy.mk x₁ :=
    hf.1.1 (ZerothHomotopy.sound γ)
  have hj : Joined x₀ x₁ := Quotient.exact he
  let α := hj.somePath
  let a : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ :=
    Path.Homotopic.Quotient.mk α
  let c : FundamentalGroupoid.mk (f x₀) ⟶ FundamentalGroupoid.mk (f x₁) :=
    Path.Homotopic.Quotient.mk γ
  let F := FundamentalGroupoid.map f
  let fa : FundamentalGroupoid.mk (f x₀) ⟶ FundamentalGroupoid.mk (f x₁) := F.map a
  obtain ⟨b, hb⟩ := fundamentalGroup_map_surjective f x₀ (hf.2 0 x₀).2 (c ≫ inv fa)
  obtain ⟨β, hβ⟩ := Path.Homotopic.Quotient.mk_surjective b
  refine ⟨β.trans α, Path.Homotopic.Quotient.exact ?_⟩
  change F.map ((Path.Homotopic.Quotient.mk β) ≫ a) = c
  rw [Functor.map_comp, hβ]
  change FundamentalGroup.map f x₀ b ≫ fa = c
  rw [hb, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end

end Thomason.Construction

end

end OAI
