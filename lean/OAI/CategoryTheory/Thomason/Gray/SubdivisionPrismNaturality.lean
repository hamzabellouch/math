import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionWeakLifting

namespace OAI

section

/-! # Stationarity of the subdivision comparison prism

The ordered comparison selects one of its endpoints at each vertex.  A
poset map identifying those endpoints therefore makes the whole prism
constant.  Applied to greatest vertices, this strengthens the double
last-vertex comparison to an exact relative homotopy.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder MonoidalCategory
  CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

theorem PosetGeometry.orderedVertexHomotopy_postcompose_stationary
    {K : SSet.{0}} {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f g : K ⟶ nerve P)
    (hfg : ∀ v : K _⦋0⦌, (f.app _ v).obj 0 ≤ (g.app _ v).obj 0)
    (v : P →o Q) (he : f ≫ nerveMap v.monotone.functor =
      g ≫ nerveMap v.monotone.functor) :
    (PosetGeometry.orderedVertexHomotopy f g hfg).h ≫ nerveMap v.monotone.functor =
      fst K Δ[1] ≫ f ≫ nerveMap v.monotone.functor := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply nerve.ext_of_isThin
  funext i
  change v (if (SSet.stdSimplex.objEquiv t).toOrderHom i = 0 then
    (f.app d s).obj i else (g.app d s).obj i) = v ((f.app d s).obj i)
  split_ifs
  · rfl
  · exact (congrArg (fun q => (q.app d s).obj i) he).symm

theorem simplexDoublePrism_stationary (n : SimplexCategory) :
    simplexDoublePrism n ≫ simplexLastVertex.app n =
      fst (SSet.sd.obj (SimplexCategory.sd.obj n)) Δ[1] ≫
        simplexDoubleFirst n ≫ simplexLastVertex.app n := by
  let v : NonemptyFiniteChains (ULift.{0} (Fin (n.len+1))) →o
      ULift.{0} (Fin (n.len+1)) := chainMaximumHom
  have he : simplexDoubleFirst n ≫ nerveMap v.monotone.functor =
      simplexDoubleLast n ≫ nerveMap v.monotone.functor := by
    apply (cancel_mono (originalSimplexIso n).inv).mp
    change simplexDoubleFirst n ≫ simplexLastVertex.app n =
      simplexDoubleLast n ≫ simplexLastVertex.app n
    dsimp only [simplexDoubleFirst, simplexDoubleLast]
    rw [Category.assoc, lastVertex_standard_formula]
    exact lastVertex.naturality (simplexLastVertex.app n)
  have h := PosetGeometry.orderedVertexHomotopy_postcompose_stationary
    (simplexDoubleFirst n) (simplexDoubleLast n) (simplexDoubleFirst_le n) v he
  have h' := congrArg (fun q => q ≫ (originalSimplexIso n).inv) h
  have hv : nerveMap v.monotone.functor ≫ (originalSimplexIso n).inv =
      simplexLastVertex.app n := rfl
  change (simplexDoublePrism n ≫ nerveMap v.monotone.functor) ≫
    (originalSimplexIso n).inv = (fst _ Δ[1] ≫ simplexDoubleFirst n ≫
      nerveMap v.monotone.functor) ≫ (originalSimplexIso n).inv at h'
  have hl : (simplexDoublePrism n ≫ nerveMap v.monotone.functor) ≫
      (originalSimplexIso n).inv = simplexDoublePrism n ≫ simplexLastVertex.app n :=
    (Category.assoc (simplexDoublePrism n) (nerveMap v.monotone.functor)
      (originalSimplexIso n).inv).trans (congrArg (simplexDoublePrism n ≫ ·) hv)
  have hi : (simplexDoubleFirst n ≫ nerveMap v.monotone.functor) ≫
      (originalSimplexIso n).inv = simplexDoubleFirst n ≫ simplexLastVertex.app n :=
    (Category.assoc (simplexDoubleFirst n) (nerveMap v.monotone.functor)
      (originalSimplexIso n).inv).trans (congrArg (simplexDoubleFirst n ≫ ·) hv)
  have hr : (fst _ Δ[1] ≫ simplexDoubleFirst n ≫ nerveMap v.monotone.functor) ≫
      (originalSimplexIso n).inv = fst _ Δ[1] ≫ simplexDoubleFirst n ≫
        simplexLastVertex.app n :=
    (Category.assoc (fst _ Δ[1]) (simplexDoubleFirst n ≫ nerveMap v.monotone.functor)
      (originalSimplexIso n).inv).trans (congrArg (fst _ Δ[1] ≫ ·) hi)
  exact hl.symm.trans (h'.trans hr)

theorem standardDoubleHomotopy_stationary (n : SimplexCategory) :
    (standardDoubleHomotopy n).h ≫ lastVertex.app (SSet.stdSimplex.obj n) =
      fst (SSet.sd.obj (SSet.sd.obj (SSet.stdSimplex.obj n))) Δ[1] ≫
        SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj n)) ≫
          lastVertex.app (SSet.stdSimplex.obj n) := by
  change ((SSet.sd.map (SSet.stdSimplex.sdIso.hom.app n) ▷ Δ[1]) ≫
    simplexDoublePrism n ≫ SSet.stdSimplex.sdIso.inv.app n) ≫
      lastVertex.app (SSet.stdSimplex.obj n) = _
  rw [Category.assoc, Category.assoc, lastVertex_on_standard_simplex]
  rw [simplexDoublePrism_stationary]
  simp only [← Category.assoc, whiskerRight_fst]
  have h := simplexDoubleFirst_conjugate n
  have h' := congrArg (fun q => q ≫ lastVertex.app (SSet.stdSimplex.obj n)) h
  rw [Category.assoc, Category.assoc, lastVertex_on_standard_simplex] at h'
  exact congrArg (fst _ Δ[1] ≫ ·) h'

@[reassoc]
theorem subdivisionLastVertexHomotopy_fac (K : SSet.{0})
    (j : CostructuredArrow SSet.stdSimplex K) :
    (SSet.sd.map (SSet.sd.map j.hom) ▷ Δ[1]) ≫ (subdivisionLastVertexHomotopy K).h =
      (standardDoubleHomotopy j.left).h ≫ SSet.sd.map j.hom := by
  exact SimplicialHomotopyDescent.assemble_fac (SSet.sd ⋙ SSet.sd) K (SSet.sd.obj K)
    (doubleLastVertexPiece K) (doubleLastVertexPiece_naturality K) j

theorem subdivisionLastVertexHomotopy_stationary (K : SSet.{0}) :
    (subdivisionLastVertexHomotopy K).h ≫ lastVertex.app K =
      fst (SSet.sd.obj (SSet.sd.obj K)) Δ[1] ≫
        SSet.sd.map (lastVertex.app K) ≫ lastVertex.app K := by
  apply (isColimitOfPreserves (tensorRight (Δ[1] : SSet.{0}))
    (SimplicialHomotopyDescent.isColimit (SSet.sd ⋙ SSet.sd) K)).hom_ext
  intro j
  change (SSet.sd.map (SSet.sd.map j.hom) ▷ Δ[1]) ≫ _ =
    (SSet.sd.map (SSet.sd.map j.hom) ▷ Δ[1]) ≫ _
  rw [← Category.assoc, subdivisionLastVertexHomotopy_fac]
  rw [Category.assoc, lastVertex.naturality j.hom,
    ← Category.assoc, standardDoubleHomotopy_stationary]
  simp only [← Category.assoc, whiskerRight_fst]
  have hn : SSet.sd.map (SSet.sd.map j.hom) ≫ SSet.sd.map (lastVertex.app K) =
      SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj j.left)) ≫ SSet.sd.map j.hom := by
    rw [← SSet.sd.map_comp, lastVertex.naturality j.hom, SSet.sd.map_comp]
    rfl
  have hc : SSet.sd.map (SSet.sd.map j.hom) ≫ SSet.sd.map (lastVertex.app K) ≫
      lastVertex.app K = SSet.sd.map (lastVertex.app (SSet.stdSimplex.obj j.left)) ≫
        lastVertex.app (SSet.stdSimplex.obj j.left) ≫ j.hom := by
    rw [← Category.assoc, hn, Category.assoc, lastVertex.naturality j.hom]
    rfl
  simpa only [Category.assoc, Functor.id_map] using congrArg (fst _ Δ[1] ≫ ·) hc.symm

local instance : SSet.ex.{0}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _

theorem extensionCylinder_fst (X : SSet.{0}) :
    extensionCylinder X ≫ SSet.ex.map (fst X Δ[1]) = fst (SSet.ex.obj X) Δ[1] := by
  simp [extensionCylinder]

/-- The unit comparison homotopy is constant after extension of the
last-vertex map. This is the exact relative identity used for descent
over a prescribed base. -/
theorem subdivisionUnitHomotopy_stationary (K : SSet.{0}) :
    (subdivisionUnitHomotopy K).h ≫ SSet.ex.map (lastVertex.app K) =
      fst (SSet.sd.obj K) Δ[1] ≫ lastVertex.app K ≫ canonicalExtension.app K := by
  have hu : SSet.sdExAdjunction.unit.app K ≫ SSet.ex.map (lastVertex.app K) =
      canonicalExtension.app K :=
    (SSet.sdExAdjunction.homEquiv_unit K K (lastVertex.app K)).symm
  change ((SSet.sdExAdjunction.unit.app (SSet.sd.obj K) ▷ Δ[1]) ≫
    extensionCylinder (SSet.sd.obj (SSet.sd.obj K)) ≫
      SSet.ex.map (subdivisionLastVertexHomotopy K).h) ≫
        SSet.ex.map (lastVertex.app K) = _
  calc
    _ = (SSet.sdExAdjunction.unit.app (SSet.sd.obj K) ▷ Δ[1]) ≫
        extensionCylinder (SSet.sd.obj (SSet.sd.obj K)) ≫
          SSet.ex.map ((subdivisionLastVertexHomotopy K).h ≫ lastVertex.app K) := by
      rw [SSet.ex.map_comp]
      simp only [Category.assoc]
    _ = (SSet.sdExAdjunction.unit.app (SSet.sd.obj K) ▷ Δ[1]) ≫
        extensionCylinder (SSet.sd.obj (SSet.sd.obj K)) ≫
          SSet.ex.map (fst (SSet.sd.obj (SSet.sd.obj K)) Δ[1] ≫
            SSet.sd.map (lastVertex.app K) ≫ lastVertex.app K) := by
      rw [subdivisionLastVertexHomotopy_stationary]
    _ = fst (SSet.sd.obj K) Δ[1] ≫ SSet.sdExAdjunction.unit.app (SSet.sd.obj K) ≫
        SSet.ex.map (SSet.sd.map (lastVertex.app K)) ≫ SSet.ex.map (lastVertex.app K) := by
      simp only [SSet.ex.map_comp, ← Category.assoc, extensionCylinder_fst,
        whiskerRight_fst, Functor.id_obj]
    _ = fst (SSet.sd.obj K) Δ[1] ≫ lastVertex.app K ≫
        SSet.sdExAdjunction.unit.app K ≫ SSet.ex.map (lastVertex.app K) := by
      have hn : SSet.sdExAdjunction.unit.app (SSet.sd.obj K) ≫
          SSet.ex.map (SSet.sd.map (lastVertex.app K)) =
          lastVertex.app K ≫ SSet.sdExAdjunction.unit.app K :=
        (SSet.sdExAdjunction.unit.naturality (lastVertex.app K)).symm
      simpa only [Category.assoc] using congrArg
        (fun q => fst (SSet.sd.obj K) Δ[1] ≫ q ≫ SSet.ex.map (lastVertex.app K)) hn
    _ = _ := by rw [hu]

end

end Thomason.Construction

end

section

/-! # Naturality of the relative subdivision prism -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

@[reassoc]
theorem subdivisionLastVertexHomotopy_naturality {A B : SSet.{0}} (f : A ⟶ B) :
    (SSet.sd.map (SSet.sd.map f) ▷ Δ[1]) ≫ (subdivisionLastVertexHomotopy B).h =
      (subdivisionLastVertexHomotopy A).h ≫ SSet.sd.map f := by
  apply (isColimitOfPreserves (tensorRight (Δ[1] : SSet.{0}))
    (SimplicialHomotopyDescent.isColimit (SSet.sd ⋙ SSet.sd) A)).hom_ext
  intro j
  change (SSet.sd.map (SSet.sd.map j.hom) ▷ Δ[1]) ≫
      ((SSet.sd.map (SSet.sd.map f) ▷ Δ[1]) ≫ (subdivisionLastVertexHomotopy B).h) =
    (SSet.sd.map (SSet.sd.map j.hom) ▷ Δ[1]) ≫
      ((subdivisionLastVertexHomotopy A).h ≫ SSet.sd.map f)
  have hc : SSet.sd.map (SSet.sd.map j.hom) ≫ SSet.sd.map (SSet.sd.map f) =
      SSet.sd.map (SSet.sd.map (j.hom ≫ f)) := by
    rw [← SSet.sd.map_comp, ← SSet.sd.map_comp]
  let j' : CostructuredArrow SSet.stdSimplex B := CostructuredArrow.mk (j.hom ≫ f)
  calc
    _ = (SSet.sd.map (SSet.sd.map (j.hom ≫ f)) ▷ Δ[1]) ≫
        (subdivisionLastVertexHomotopy B).h := by
      rw [← Category.assoc, ← comp_whiskerRight, hc]
    _ = (standardDoubleHomotopy j.left).h ≫ SSet.sd.map (j.hom ≫ f) :=
      subdivisionLastVertexHomotopy_fac B j'
    _ = ((standardDoubleHomotopy j.left).h ≫ SSet.sd.map j.hom) ≫ SSet.sd.map f := by
      rw [SSet.sd.map_comp, Category.assoc]
    _ = _ := by rw [← subdivisionLastVertexHomotopy_fac, Category.assoc]

local instance : SSet.ex.{0}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts _

@[reassoc]
theorem extensionCylinder_naturality {A B : SSet.{0}} (f : A ⟶ B) :
    (SSet.ex.map f ▷ Δ[1]) ≫ extensionCylinder B =
      extensionCylinder A ≫ SSet.ex.map (f ▷ Δ[1]) := by
  simp only [extensionCylinder, id_tensorHom]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left, Category.assoc]

@[reassoc]
theorem subdivisionUnitHomotopy_naturality {A B : SSet.{0}} (f : A ⟶ B) :
    (SSet.sd.map f ▷ Δ[1]) ≫ (subdivisionUnitHomotopy B).h =
      (subdivisionUnitHomotopy A).h ≫ SSet.ex.map (SSet.sd.map f) := by
  have hn : SSet.sd.map f ≫ SSet.sdExAdjunction.unit.app (SSet.sd.obj B) =
      SSet.sdExAdjunction.unit.app (SSet.sd.obj A) ≫
        SSet.ex.map (SSet.sd.map (SSet.sd.map f)) :=
    SSet.sdExAdjunction.unit.naturality (SSet.sd.map f)
  change (SSet.sd.map f ▷ Δ[1]) ≫
      ((SSet.sdExAdjunction.unit.app (SSet.sd.obj B) ▷ Δ[1]) ≫
        extensionCylinder (SSet.sd.obj (SSet.sd.obj B)) ≫
          SSet.ex.map (subdivisionLastVertexHomotopy B).h) =
    ((SSet.sdExAdjunction.unit.app (SSet.sd.obj A) ▷ Δ[1]) ≫
      extensionCylinder (SSet.sd.obj (SSet.sd.obj A)) ≫
        SSet.ex.map (subdivisionLastVertexHomotopy A).h) ≫ SSet.ex.map (SSet.sd.map f)
  rw [← Category.assoc, ← comp_whiskerRight, hn, comp_whiskerRight]
  simp only [Category.assoc]
  rw [extensionCylinder_naturality_assoc, ← SSet.ex.map_comp,
    subdivisionLastVertexHomotopy_naturality, SSet.ex.map_comp]

end

end Thomason.Construction

end

end OAI
