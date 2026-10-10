import Mathlib

namespace OAI

noncomputable section
instance matMeas (n m : Type*) : MeasurableSpace (Matrix n m ℂ) := borel _
instance matBorel (n m : Type*) : BorelSpace (Matrix n m ℂ) := ⟨rfl⟩
variable {n : Type}

lemma matrix_sub_continuous : Continuous (fun x : Matrix n n ℂ × Matrix n n ℂ => x.1-x.2) := by fun_prop
open scoped Matrix.Norms.L2Operator

end

end OAI
