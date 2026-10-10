import OAI.CategoryTheory.Globular.CutoffExpansion

namespace OAI

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits
namespace GlobularSet

theorem exactBoundaryTest_at_of_low_square.{v} {X Y R S : GlobularSet.{v}}
    (i : Hom X Y) (j : Hom R S) (a : Hom X R) (b : Hom Y S)
    (sq : i.comp b = a.comp j) (hj : ExactBoundaryTest j) (d : ℕ)
    (ha : ∀ k, k ≤ d → Function.Bijective (a.app k))
    (hb : Function.Injective (b.app d)) (hb₁ : Function.Surjective (b.app (d+1)))
    (bd : X.Boundary d) (y : Y.Cell d) (hy : Y.boundary d y = i.boundaryMap d bd) :
    ∃ x : X.Cell d, X.boundary d x = bd ∧ Y.Joined d (i.app d x) y := by
  have hy' : S.boundary d (b.app d y) = j.boundaryMap d (a.boundaryMap d bd) := by
    rw [← b.boundary_app,hy, ← Hom.boundaryMap_comp, sq, Hom.boundaryMap_comp]
  obtain ⟨r,hr,z,zs,zt⟩ := hj d (a.boundaryMap d bd) (b.app d y) hy'
  obtain ⟨x,hx⟩ := (ha d le_rfl).surjective r
  have hxbd : X.boundary d x = bd := by
    apply (Hom.boundaryMap_bijective_of_low a d (fun k hk => ha k (by omega))).injective
    rw [a.boundary_app,hx,hr]
  obtain ⟨c,hc⟩ := hb₁ z
  have hsquare : b.app d (i.app d x) = j.app d (a.app d x) :=
    congrFun (congrArg (fun f => f.app d) sq) x
  refine ⟨x,hxbd,c, ?_, ?_⟩
  · apply hb
    rw [b.source_app,hc,zs,hsquare,hx]
  · apply hb
    rw [b.target_app,hc,zt]

end GlobularSet

theorem elementary_expansion.{v} (C : GlobularTheory.{v}) (hC : C.IsCoherator)
    (X : C.Model) (hX : X.IsCellular) (n : ℕ)
    (a : GlobularTheory.Model.disk C n ⟶ X)
    (Y : C.Model) (i : X ⟶ Y)
    (b : GlobularTheory.Model.disk C (n + 1) ⟶ Y)
    (square : IsPushout a (GlobularTheory.Model.J C n) i b) :
    GlobularTheory.Model.WeakEquivalence hC i := by
  apply GlobularTheory.Model.weakEquivalence_of_exactBoundaryTest hC
  intro d bd y hy
  let q := max (n+1) (d+1)
  have hnq : n ≤ q := by dsimp [q]; omega
  have hdq : d ≤ q := by dsimp [q]; omega
  have hd₁q : d+1 ≤ q := Nat.le_max_right _ _
  let F := GlobularTheory.Model.cutoffFunctor hC q
  let ηX := GlobularTheory.Model.underlyingMap
    (GlobularTheory.Model.cutoffUnit hC q X)
  let ηY := GlobularTheory.Model.underlyingMap
    (GlobularTheory.Model.cutoffUnit hC q Y)
  have hs : (GlobularTheory.Model.underlyingMap i).comp ηY =
      ηX.comp (GlobularTheory.Model.underlyingMap (F.map i).hom) :=
    congrArg GlobularTheory.Model.underlyingMap
      ((GlobularTheory.Model.cutoffAdjunction hC q).unit.naturality i)
  exact GlobularSet.exactBoundaryTest_at_of_low_square
    (GlobularTheory.Model.underlyingMap i)
    (GlobularTheory.Model.underlyingMap (F.map i).hom) ηX ηY hs
    (GlobularTheory.Model.cutoff_elementary_exactBoundaryTest hC q n hnq hX a i b square)
    d (fun k hk => GlobularTheory.Model.cutoffUnit_low_bijective hC q X k (hk.trans hdq))
    (GlobularTheory.Model.cutoffUnit_low_bijective hC q Y d hdq).injective
    (GlobularTheory.Model.cutoffUnit_low_bijective hC q Y (d+1) hd₁q).surjective bd y hy

end Grothendieck

end OAI
