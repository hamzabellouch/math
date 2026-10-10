import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationLeaves

namespace OAI

namespace Ostmann.Tree.QuartetFactorization
noncomputable section
open scoped BigOperators
open Density
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

structure Frame (F : Type*) [Field F] where
  parameters : Parameters F 2
  leftCurrent : Fˣ
  rightCurrent : Fˣ
  coefficient : Fˣ

namespace Frame

def value (f : Frame F) (g : F → ℂ) (D : Fˣ) (M : Leaves 2 → Fˣ) : ℂ :=
  f.parameters.evaluate g D f.leftCurrent f.rightCurrent 0 M

def argument (f : Frame F) (D total : Fˣ) : Fˣ :=
  f.parameters.frequency / (D*f.leftCurrent*f.rightCurrent*f.coefficient*total)

end Frame

def propagate : (k : ℕ) → Parameters F (k+2) → Fˣ → Fˣ → Fˣ →
    (Leaves k → Fˣ) → Option (Leaves k → Frame F)
  | 0, P, Xl, Xr, c, _ => some (fun _ => ⟨P, Xl, Xr, c⟩)
  | k+1, .branch s a b u L R, Xl, Xr, _, totals =>
      if hp : Density.pivot s a b u ((bottomCut k).parameters L)
          ((bottomCut k).parameters R) Xl Xr totals = 0 then none else
        let p := Units.mk0 _ hp
        match propagate k L p Xl (u*a) (left totals),
          propagate k R p Xr (u*b) (right totals) with
        | some fl, some fr => some (join fl fr)
        | _, _ => none

theorem propagate_project_split (k : ℕ) (s a b u Xl Xr c : Fˣ)
    (L R : Parameters F (k+2)) (M : Leaves (k+3) → Fˣ) :
    propagate (k+1) (.branch s a b u L R) Xl Xr c
      ((bottomCut (k+1)).project M) =
      if hp : Density.pivot s a b u L R Xl Xr M = 0 then none else
        match propagate k L (Units.mk0 _ hp) Xl (u*a) ((bottomCut k).project (left M)),
          propagate k R (Units.mk0 _ hp) Xr (u*b) ((bottomCut k).project (right M)) with
        | some fl, some fr => some (join fl fr)
        | _, _ => none := by
  simp only [propagate, bottomCut, Density.Cut.project_pivot]
  simp only [Density.Cut.project, left_join, right_join]

def frameProduct {k : ℕ} (g : F → ℂ) (D : Fˣ) (M : Leaves k → Leaves 2 → Fˣ)
    (frames : Option (Leaves k → Frame F)) : ℂ :=
  match frames with
  | none => 0
  | some fs => ∏ v, (fs v).value g D (M v)

theorem frameProduct_join {k : ℕ} (g : F → ℂ) (D : Fˣ)
    (Ml Mr : Leaves k → Leaves 2 → Fˣ) (fl fr : Option (Leaves k → Frame F)) :
    frameProduct g D (join Ml Mr)
      (match fl, fr with | some l, some r => some (join l r) | _, _ => none) =
      frameProduct g D Ml fl * frameProduct g D Mr fr := by
  cases fl <;> cases fr <;> simp only [frameProduct, zero_mul, mul_zero]
  rw [Density.prod_split]
  congr 1

theorem evaluate_incoming_irrelevant {d : ℕ} (P : Parameters F (d+1))
    (g : F → ℂ) (D Xl Xr : Fˣ) (incoming : F) (M : Leaves (d+1) → Fˣ) :
    P.evaluate g D Xl Xr incoming M = P.evaluate g D Xl Xr 0 M := by
  cases P
  rfl

theorem evaluate_factorization (k : ℕ) (P : Parameters F (k+2))
    (g : F → ℂ) (D Xl Xr c : Fˣ) (incoming : F) (M : Leaves (k+2) → Fˣ) :
    P.evaluate g D Xl Xr incoming M =
      frameProduct g D (bottomLeaves k M)
        (propagate k P Xl Xr c ((bottomCut k).project M)) := by
  induction k generalizing Xl Xr c incoming with
  | zero =>
    simp only [propagate, frameProduct, bottomLeaves, Frame.value]
    simpa using evaluate_incoming_irrelevant P g D Xl Xr incoming M
  | succ k ih =>
    cases P with
    | branch s a b u L R =>
      rw [propagate_project_split]
      change (if hp : Density.pivot s a b u L R Xl Xr M = 0 then 0 else
        L.evaluate g D (Units.mk0 _ hp) Xl
          ((L.frequency : F) / ((D:F)*(Units.mk0 _ hp:Fˣ)*u*
            (Xl*a*Parameters.leafProduct (left M)))) (left M) *
        R.evaluate g D (Units.mk0 _ hp) Xr
          ((R.frequency : F) / ((D:F)*(Units.mk0 _ hp:Fˣ)*u*
            (Xr*b*Parameters.leafProduct (right M)))) (right M)) = _
      by_cases hp : Density.pivot s a b u L R Xl Xr M = 0
      · simp [hp, frameProduct]
      · simp only [dite_eq_right hp, bottomLeaves]
        rw [ih L _ _ (u*a), ih R _ _ (u*b)]
        exact (frameProduct_join g D _ _ _ _).symm

end
end Ostmann.Tree.QuartetFactorization

end OAI
