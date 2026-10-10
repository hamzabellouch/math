import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationFrames

namespace OAI

namespace Ostmann.Tree.QuartetFactorization
noncomputable section
open scoped BigOperators
open Density
variable {F : Type*} [Field F]
local instance quartetFactorizationArgumentsDecidableEq : DecidableEq F := Classical.decEq F

def frameArguments {k : ℕ} (D : Fˣ) (totals : Leaves k → Fˣ)
    (frames : Option (Leaves k → Frame F)) : Option (Leaves k → Fˣ) :=
  frames.map (fun fs v => (fs v).argument D (totals v))

theorem frameArguments_split {k : ℕ} (D : Fˣ) (totals : Leaves (k+1) → Fˣ)
    (fl fr : Option (Leaves k → Frame F)) :
    frameArguments D totals
      (match fl, fr with | some l, some r => some (join l r) | _, _ => none) =
      match frameArguments D (left totals) fl, frameArguments D (right totals) fr with
      | some yl, some yr => some (join yl yr)
      | _, _ => none := by
  cases fl <;> cases fr <;> simp only [frameArguments, Option.map_none, Option.map_some]
  congr 1
  funext v
  have he := congrArg (fun x => x v) (join_left_right totals)
  cases hv : v 0 <;> simp only [join, hv, Bool.false_eq_true, ↓reduceIte] at he ⊢ <;> rw [he]

theorem propagate_arguments (k : ℕ) (P : Parameters F (k+2))
    (D Xl Xr c : Fˣ) (totals : Leaves k → Fˣ) :
    frameArguments D totals (propagate k P Xl Xr c totals) =
      Density.reconstruct D ((bottomCut k).parameters P) Xl Xr c totals := by
  induction k generalizing Xl Xr c with
  | zero =>
    simp [frameArguments, propagate, bottomCut, Density.Cut.parameters,
      Density.reconstruct, Frame.argument, rootArgument, Parameters.frequency,
      Parameters.leafProduct]
    funext v
    apply congrArg (fun z : Fˣ => P.frequency / (D*Xl*Xr*c*z))
    exact congrArg totals (Subsingleton.elim _ _)
  | succ k ih =>
    cases P with
    | branch s a b u L R =>
      simp only [propagate, bottomCut, Density.Cut.parameters, Density.reconstruct]
      by_cases hp : Density.pivot s a b u ((bottomCut k).parameters L)
          ((bottomCut k).parameters R) Xl Xr totals = 0
      · simp [hp, frameArguments]
      · simp only [dite_eq_right hp]
        rw [← ih L _ _ (u*a), ← ih R _ _ (u*b)]
        exact frameArguments_split D totals _ _

theorem frame_argument_actual_leaves (k : ℕ) (D : Fˣ) (M : Leaves (k+2) → Fˣ)
    (fs : Leaves k → Frame F) (v : Leaves k) :
    (fs v).argument D ((bottomCut k).project M v) =
      Density.rootArgument (fs v).parameters D (fs v).leftCurrent (fs v).rightCurrent
        (fs v).coefficient (bottomLeaves k M v) := by
  unfold Frame.argument Density.rootArgument
  rw [bottomLeaves_product]

end
end Ostmann.Tree.QuartetFactorization

end OAI
