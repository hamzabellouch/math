import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationFrames

namespace OAI

namespace Ostmann.Tree.QuartetFactorization
noncomputable section
open Density
variable {F : Type*} [Field F]
local instance quartetFactorizationValidityDecidableEq : DecidableEq F := Classical.decEq F

theorem propagate_validity (k : ℕ) (P : Parameters F (k+2))
    (hP : P.consistent) (Xl Xr c : Fˣ) (hc : P.childConsistent c)
    (totals : Leaves k → Fˣ) (fs : Leaves k → Frame F)
    (h : propagate k P Xl Xr c totals = some fs) (v : Leaves k) :
    (fs v).parameters = bottomParameters k P v ∧
      (fs v).parameters.childConsistent (fs v).coefficient := by
  induction k generalizing Xl Xr c with
  | zero =>
    simp only [propagate, Option.some.injEq] at h
    rw [← h]
    exact ⟨rfl, hc⟩
  | succ k ih =>
    cases P with
    | branch s a b u L R =>
      simp only [propagate] at h
      split at h
      · contradiction
      · split at h <;> try contradiction
        rename_i fl fr hfl hfr
        have hfs := Option.some.inj h
        rw [← hfs]
        cases hv : v 0 <;>
          simp only [join, bottomParameters, hv, Bool.false_eq_true, ↓reduceIte]
        · exact ih L hP.2.2.1 _ Xl (u*a) hP.1 _ fl hfl _
        · exact ih R hP.2.2.2 _ Xr (u*b) hP.2.1 _ fr hfr _

theorem Frame.coefficient_eq_rootCoefficient (f : Frame F)
    (hc : f.parameters.childConsistent f.coefficient) :
    f.coefficient = Density.rootCoefficient f.parameters := by
  cases hp : f.parameters with
  | branch s a b u L R =>
    rw [hp] at hc
    exact hc.symm

end
end Ostmann.Tree.QuartetFactorization

end OAI
