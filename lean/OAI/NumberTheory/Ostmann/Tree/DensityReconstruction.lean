import OAI.NumberTheory.Ostmann.Tree.Diagram

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F]

namespace Density

def left {d : ℕ} {A : Type*} (M : Leaves (d+1) → A) : Leaves d → A :=
  fun v => M (Fin.cons false v)
def right {d : ℕ} {A : Type*} (M : Leaves (d+1) → A) : Leaves d → A :=
  fun v => M (Fin.cons true v)
def join {d : ℕ} {A : Type*} (L R : Leaves d → A) : Leaves (d+1) → A :=
  fun v => if v 0 then R (Fin.tail v) else L (Fin.tail v)

@[simp] theorem left_join {d : ℕ} {A : Type*} (L R : Leaves d → A) :
    left (join L R) = L := by funext v; simp [left, join]
@[simp] theorem right_join {d : ℕ} {A : Type*} (L R : Leaves d → A) :
    right (join L R) = R := by funext v; simp [right, join]
@[simp] theorem join_left_right {d : ℕ} {A : Type*} (M : Leaves (d+1) → A) :
    join (left M) (right M) = M := by
  funext v
  simp only [join, left, right]
  have hv := Fin.cons_self_tail v
  cases h : v 0 <;> rw [h] at hv <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact congrArg M hv

theorem assignment_injective {d : ℕ} {A : Type*} :
    Function.Injective (fun M : Leaves (d+1) → A => (left M, right M)) := by
  intro M N h
  rw [← join_left_right M, ← join_left_right N, Prod.mk.inj h |>.1, Prod.mk.inj h |>.2]

def pathEquiv (d : ℕ) : Bool × Leaves d ≃ Leaves (d+1) where
  toFun v := Fin.cons v.1 v.2
  invFun v := (v 0, Fin.tail v)
  left_inv v := by cases v; simp
  right_inv v := Fin.cons_self_tail v

theorem prod_split {d : ℕ} {A : Type*} [CommMonoid A] (M : Leaves (d+1) → A) :
    (∏ v, M v) = (∏ v, left M v) * ∏ v, right M v := by
  rw [← (pathEquiv d).prod_comp]
  rw [Fintype.prod_prod_type]
  simp [left, right, pathEquiv, mul_comm]

theorem leafProduct_split {d : ℕ} (M : Leaves (d+1) → Fˣ) :
    Parameters.leafProduct M = Parameters.leafProduct (left M) *
      Parameters.leafProduct (right M) := prod_split M

def rootArgument {d : ℕ} (P : Parameters F d) (D Xl Xr c : Fˣ)
    (M : Leaves d → Fˣ) : Fˣ :=
  P.frequency / (D*Xl*Xr*c*Parameters.leafProduct M)

def pivot {d : ℕ} (s a b u : Fˣ) (L R : Parameters F d)
    (Xl Xr : Fˣ) (M : Leaves (d+1) → Fˣ) : F :=
  ((L.frequency : F)*(Xr*b*Parameters.leafProduct (right M)) -
    (R.frequency : F)*(Xl*a*Parameters.leafProduct (left M))) / ((s : F)*u)

local instance : DecidableEq F := Classical.decEq F

def reconstruct (D : Fˣ) : {d : ℕ} → Parameters F d → Fˣ → Fˣ → Fˣ →
    (Leaves d → Fˣ) → Option (Leaves d → Fˣ)
  | _, P@(.leaf _ _), Xl, Xr, c, M => some (fun _ => rootArgument P D Xl Xr c M)
  | _, .branch s a b u L R, Xl, Xr, _, M =>
    if hp : pivot s a b u L R Xl Xr M = 0 then none else
      let p := Units.mk0 _ hp
      match reconstruct D L p Xl (u*a) (left M),
        reconstruct D R p Xr (u*b) (right M) with
      | some yl, some yr => some (join yl yr)
      | _, _ => none

def difference : {d : ℕ} → (Leaves d → Fˣ) → F
  | 0, y => y (fun i => Fin.elim0 i)
  | _+1, y => difference (left y) - difference (right y)

@[simp] theorem difference_join {d : ℕ} (yl yr : Leaves d → Fˣ) :
    difference (join yl yr) = difference yl - difference yr := by
  simp [difference]

theorem reconstruct_branch_some {d : ℕ} (s a b u D Xl Xr c : Fˣ)
    (L R : Parameters F d) (M y : Leaves (d+1) → Fˣ)
    (h : reconstruct D (.branch s a b u L R) Xl Xr c M = some y) :
    ∃ hp : pivot s a b u L R Xl Xr M ≠ 0,
      reconstruct D L (Units.mk0 _ hp) Xl (u*a) (left M) = some (left y) ∧
      reconstruct D R (Units.mk0 _ hp) Xr (u*b) (right M) = some (right y) := by
  classical
  simp only [reconstruct] at h
  split at h
  · contradiction
  · rename_i hp
    refine ⟨hp, ?_⟩
    split at h <;> try contradiction
    rename_i yl yr hl hr
    have hy : join yl yr = y := Option.some.inj h
    rw [← hy, left_join, right_join]
    exact ⟨hl, hr⟩

end Density
end
end Ostmann.Tree

end OAI
