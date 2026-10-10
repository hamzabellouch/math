import OAI.NumberTheory.Ostmann.Arithmetic.GroupHaarImage
import OAI.NumberTheory.Ostmann.Tree.DensityAlgebra

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F]

inductive Cut : ℕ → ℕ → Type
  | stop (d : ℕ) : Cut d 0
  | split {d k : ℕ} (left right : Cut d k) : Cut (d+1) (k+1)

namespace Cut

def ofLE {d k : ℕ} (h : k ≤ d) : Cut d k := by
  induction k generalizing d with
  | zero => exact .stop d
  | succ k ih =>
    cases d with
    | zero => omega
    | succ d => exact .split (ih (by omega)) (ih (by omega))

def project : {d k : ℕ} → Cut d k → (Leaves d → Fˣ) → (Leaves k → Fˣ)
  | _, _, .stop _, M => fun _ => Parameters.leafProduct M
  | _, _, .split L R, M => join (project L (left M)) (project R (right M))

def parameters : {d k : ℕ} → Cut d k → Parameters F d → Parameters F k
  | _, _, .stop _, P => .leaf P.frequency false
  | _, _, .split L R, .branch s a b u PL PR =>
    .branch s a b u (parameters L PL) (parameters R PR)

@[simp] theorem parameters_frequency {d k : ℕ} (C : Cut d k) (P : Parameters F d) :
    (parameters C P).frequency = P.frequency := by
  cases C with
  | stop => rfl
  | split L R => cases P; rfl

theorem parameters_childConsistent {d k : ℕ} (C : Cut d k) (P : Parameters F d)
    (c : Fˣ) (h : P.childConsistent c) : (parameters C P).childConsistent c := by
  cases C with
  | stop => trivial
  | split L R => cases P; exact h

theorem parameters_consistent {d k : ℕ} (C : Cut d k) (P : Parameters F d)
    (h : P.consistent) : (parameters C P).consistent := by
  induction C with
  | stop => trivial
  | split L R ihl ihr =>
    cases P with
    | branch s a b u PL PR =>
      exact ⟨parameters_childConsistent L PL (u*a) h.1,
        parameters_childConsistent R PR (u*b) h.2.1, ihl PL h.2.2.1, ihr PR h.2.2.2⟩

theorem project_product {d k : ℕ} (C : Cut d k) (M : Leaves d → Fˣ) :
    Parameters.leafProduct (project C M) = Parameters.leafProduct M := by
  induction C with
  | stop => simp [project, Parameters.leafProduct]
  | split L R ihl ihr =>
    rw [project, leafProduct_split, left_join, right_join, ihl, ihr, leafProduct_split]

theorem project_one {d k : ℕ} (C : Cut d k) : project C (1 : Leaves d → Fˣ) = 1 := by
  induction C with
  | stop => funext v; simp [project, Parameters.leafProduct]
  | split L R ihl ihr =>
    change join (project L 1) (project R 1) = 1
    rw [ihl, ihr]
    funext v
    simp [join]

theorem project_mul {d k : ℕ} (C : Cut d k) (M N : Leaves d → Fˣ) :
    project C (M*N) = project C M * project C N := by
  induction C with
  | stop =>
    funext v
    simp [project, Parameters.leafProduct, Finset.prod_mul_distrib]
  | split L R ihl ihr =>
    change join (project L (left M * left N)) (project R (right M * right N)) = _
    rw [ihl, ihr]
    funext v
    cases hv : v 0 <;> simp [project, join, Pi.mul_apply, hv]

def projectHom {d k : ℕ} (C : Cut d k) : (Leaves d → Fˣ) →* (Leaves k → Fˣ) where
  toFun := project C
  map_one' := project_one C
  map_mul' := project_mul C

theorem project_surjective {d k : ℕ} (C : Cut d k) : Function.Surjective (project (F:=F) C) := by
  classical
  induction C with
  | stop d =>
    intro y
    let v : Leaves d := fun _ => false
    refine ⟨Pi.mulSingle v (y (fun i => Fin.elim0 i)), ?_⟩
    funext w
    have hw : w = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
    simp [project, Parameters.leafProduct, hw]
  | split L R ihl ihr =>
    intro y
    obtain ⟨Ml, hMl⟩ := ihl (left y)
    obtain ⟨Mr, hMr⟩ := ihr (right y)
    refine ⟨join Ml Mr, ?_⟩
    simp only [project, left_join, right_join, hMl, hMr, join_left_right]

theorem project_pivot {d k : ℕ} (L R : Cut d k) (s a b u Xl Xr : Fˣ)
    (PL PR : Parameters F d) (M : Leaves (d+1) → Fˣ) :
    pivot s a b u (parameters L PL) (parameters R PR) Xl Xr
      (project (.split L R) M) = pivot s a b u PL PR Xl Xr M := by
  simp only [pivot, project, left_join, right_join, parameters_frequency, project_product]

end Cut
end
end Ostmann.Tree.Density

end OAI
