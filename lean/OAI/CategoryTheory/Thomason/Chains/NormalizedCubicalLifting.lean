import OAI.CategoryTheory.Thomason.Simplicial.SingularAcyclicFibers
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction

namespace OAI

section

/-! # Reduce a cube with constant opposite faces to a path-space lifting problem -/

namespace Thomason.Construction.RealizedCube

open CategoryTheory

noncomputable section

def boundarySide (n : ℕ) (t : unitInterval)
    (z : Cube.boundary (Fin (n+1))) : Cube.boundary (Fin (n+2)) :=
  ⟨Fin.cons t z.val, by
    obtain ⟨i, hi⟩ := z.property
    exact ⟨i.succ, hi⟩⟩

/-- Currying a normalized boundary square reduces its dimension by one,
with the fixed-endpoint path map as the right-hand arrow. -/
theorem normalized_cube_lift {X Y : TopCat.{0}} (p : X ⟶ Y) (n : ℕ)
    {x₀ x₁ : X}
    (hp : HasLiftingProperty (boundaryInclusion n)
      (TopCat.ofHom (PathSpace.map p.hom (x := x₀) (y := x₁))))
    (a : C(Cube.boundary (Fin (n+2)), X))
    (b : C(Fin (n+2) → unitInterval, Y))
    (ha₀ : ∀ u, a (boundaryFacePoint (n+1) false u) = x₀)
    (ha₁ : ∀ u, a (boundaryFacePoint (n+1) true u) = x₁)
    (hab : ∀ z, p.hom (a z) = b z.val) :
    ∃ l : C(Fin (n+2) → unitInterval, X),
      (∀ z : Cube.boundary (Fin (n+2)), l z.val = a z) ∧
      ∀ z, p.hom (l z) = b z := by
  let P : TopCat.of (Path x₀ x₁) ⟶ TopCat.of (Path (p.hom x₀) (p.hom x₁)) :=
    TopCat.ofHom (PathSpace.map p.hom)
  let A : TopCat.of (Cube.boundary (Fin (n+1))) ⟶ TopCat.of (Path x₀ x₁) :=
    TopCat.ofHom {
      toFun z := {
        toFun t := a (boundarySide n t z)
        continuous_toFun := a.continuous.comp (by unfold boundarySide; fun_prop)
        source' := ha₀ z.val
        target' := ha₁ z.val }
      continuous_toFun := Path.continuous_uncurry_iff.mp (by
        change Continuous (fun z : Cube.boundary (Fin (n+1)) × unitInterval =>
          a (boundarySide n z.2 z.1))
        exact a.continuous.comp (by unfold boundarySide; fun_prop)) }
  let B : TopCat.of (Fin (n+1) → unitInterval) ⟶
      TopCat.of (Path (p.hom x₀) (p.hom x₁)) := TopCat.ofHom {
    toFun u := {
      toFun t := b (Fin.cons t u)
      continuous_toFun := b.continuous.comp (by fun_prop)
      source' := (hab (boundaryFacePoint (n+1) false u)).symm.trans
        (congrArg p.hom (ha₀ u))
      target' := (hab (boundaryFacePoint (n+1) true u)).symm.trans
        (congrArg p.hom (ha₁ u)) }
    continuous_toFun := Path.continuous_uncurry_iff.mp (by
      change Continuous (fun z : (Fin (n+1) → unitInterval) × unitInterval =>
        b (Fin.cons z.2 z.1))
      fun_prop) }
  have sq : CommSq A (boundaryInclusion n) P B := by
    constructor
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Path.ext
    funext t
    exact hab (boundarySide n t z)
  let : HasLiftingProperty (boundaryInclusion n) P := hp
  let l : C(Fin (n+2) → unitInterval, X) := {
    toFun z := sq.lift.hom (Fin.tail z) (z 0)
    continuous_toFun := (Path.continuous_uncurry_iff.mpr sq.lift.hom.continuous).comp
      (show Continuous (fun z : Fin (n+2) → unitInterval => (Fin.tail z, z 0)) from
        by fun_prop) }
  refine ⟨l, ?_, ?_⟩
  · intro z
    obtain ⟨i, hi⟩ := z.property
    cases i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · change sq.lift.hom (Fin.tail z.val) (z.val 0) = _
        rw [hi, Path.source]
        apply (ha₀ (Fin.tail z.val)).symm.trans
        congr 1
        apply Subtype.ext
        change Fin.cons 0 (Fin.tail z.val) = z.val
        rw [← hi, Fin.cons_self_tail]
      · change sq.lift.hom (Fin.tail z.val) (z.val 0) = _
        rw [hi, Path.target]
        apply (ha₁ (Fin.tail z.val)).symm.trans
        congr 1
        apply Subtype.ext
        change Fin.cons 1 (Fin.tail z.val) = z.val
        rw [← hi, Fin.cons_self_tail]
    | succ i =>
      let v : Cube.boundary (Fin (n+1)) := ⟨Fin.tail z.val, ⟨i, hi⟩⟩
      have he := congrArg (fun f => f.hom v (z.val 0)) sq.fac_left
      change l z.val = a (boundarySide n (z.val 0) v) at he
      refine he.trans ?_
      congr 1
      apply Subtype.ext
      exact Fin.cons_self_tail z.val
  · intro z
    have he := congrArg (fun f => f.hom (Fin.tail z) (z 0)) sq.fac_right
    change p.hom (l z) = b (Fin.cons (z 0) (Fin.tail z)) at he
    simpa only [Fin.cons_self_tail] using he

end

end Thomason.Construction.RealizedCube

end

end OAI
