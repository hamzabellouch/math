import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkCycles

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}

theorem wordArray_trace {n : ℕ} (g : Fin (n+1) → Germ M) (b : Fin n → Bool)
    (h : ∀ i : Fin n,advance (g i.castSucc) (b i)=g i.succ) :
    traced (g 0) (List.ofFn b)=List.ofFn (fun i : Fin n => (g i.castSucc).1) ∧
      terminalGerm (g 0) (List.ofFn b)=g (Fin.last n) := by
  induction n with
  | zero => simp [traced,terminalGerm]
  | succ n ih =>
    have ht : ∀ i : Fin n,advance (Fin.tail g i.castSucc) (Fin.tail b i)=Fin.tail g i.succ := by
      intro i
      exact h i.succ
    have hh:=ih (Fin.tail g) (Fin.tail b) ht
    simp only [Fin.tail] at hh
    have h0 : advance (g 0) (b 0)=g (Fin.succ 0) := h 0
    constructor
    · rw [List.ofFn_succ,traced,h0]
      have hht : traced (g (Fin.succ 0)) (List.ofFn (fun i : Fin n => b i.succ))=
          List.ofFn (fun i : Fin n => (g i.castSucc.succ).1) := hh.1
      rw [hht]
      rw [List.ofFn_succ]
      rfl
    · rw [List.ofFn_succ,terminalGerm,h0]
      exact hh.2

end PolynomialVacuumCylinder

end OAI
