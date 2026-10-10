import OAI.Computability.DegreeRigidity.Computability.ArithmeticHierarchy

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

theorem form_true (Y : Oracle) (n : ℕ) (s : Bool) : Form Y n s (fun _ => True) := by
  induction n with
  | zero =>
    classical
    simpa only [Form, RecursivePred, ↓reduceIte] using
      (total_primrec (O := {oracleFunction Y}) (Primrec.const 1))
  | succ n ih => exact ih.raise

theorem Form.finite_all {Y n s k} {P : Fin k → ℕ → Prop}
    (h : ∀ i, Form Y n s (P i)) : Form Y n s (fun x => ∀ i, P i x) := by
  induction k with
  | zero => exact (form_true Y n s).congr (fun x => by simp)
  | succ k ih =>
    exact ((h 0).and (ih (fun i => h i.succ))).congr (fun x => by
      simp only [Fin.forall_fin_succ])

end TuringRigidity.ArithmeticHierarchy

end OAI
