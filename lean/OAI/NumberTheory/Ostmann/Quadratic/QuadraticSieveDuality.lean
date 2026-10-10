import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveFinite

namespace OAI

/-! # Reciprocity and duality interchange the two quadratic-sieve lengths -/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

 theorem QuadraticSieveBound.transpose {M N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (h : QuadraticSieveBound N M K) : QuadraticSieveBound M N (2 * K) := by
  let U := oddSquarefreeRange M
  let V := oddSquarefreeRange N
  let F : Matrix U V ℂ := .of (fun m n => (jacobiSym (n.val : ℤ) m.val : ℂ))
  have hdual (b : U → ℂ) :
      (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) ≤ 2 * K * ∑ m : U, ‖b m‖ ^ 2 := by
    let b' : ℕ → ℂ := fun m => if hm : m ∈ U then b ⟨m, hm⟩ else 0
    have hE : quadraticSieveEnergy M b' = ∑ m : U, ‖b m‖ ^ 2 := by
      symm
      calc
        _ = ∑ m : U, ‖b' m.val‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro m _
          simp [b']
        _ = ∑ m ∈ U, ‖b' m‖ ^ 2 := Finset.sum_coe_sort U (fun m : ℕ => ‖b' m‖ ^ 2)
    have hpoint (n : V) : (Fᴴ *ᵥ b) n = quadraticTransposeSum M b' n.val := by
      change (∑ m : U, star ((jacobiSym (n.val : ℤ) m.val : ℂ)) * b m) = _
      calc
        _ = ∑ m : U, b' m.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
          apply Finset.sum_congr rfl
          intro m _
          simp only [star_intCast]
          simp [b', mul_comm]
        _ = _ := Finset.sum_coe_sort U (fun m : ℕ => b' m * (jacobiSym (n.val : ℤ) m : ℂ))
    have hsum : (∑ n : V, ‖(Fᴴ *ᵥ b) n‖ ^ 2) =
        ∑ n ∈ V, ‖quadraticTransposeSum M b' n‖ ^ 2 := by
      calc
        _ = ∑ n : V, ‖quadraticTransposeSum M b' n.val‖ ^ 2 := by simp_rw [hpoint]
        _ = _ := Finset.sum_coe_sort V (fun n : ℕ => ‖quadraticTransposeSum M b' n‖ ^ 2)
    rw [hsum, ← hE]
    exact quadraticTranspose_of_bound h b'
  intro b
  have hb := finite_matrix_duality F (2 * K) (by positivity) hdual (fun n => b n.val)
  have hpoint (m : U) : (F *ᵥ fun n => b n.val) m = quadraticSieveSum N b m.val := by
    change (∑ n : V, (jacobiSym (n.val : ℤ) m.val : ℂ) * b n.val) = _
    calc
      _ = ∑ n : V, b n.val * (jacobiSym (n.val : ℤ) m.val : ℂ) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = _ := Finset.sum_coe_sort V (fun n : ℕ => b n * (jacobiSym (n : ℤ) m.val : ℂ))
  have hleft : (∑ m : U, ‖(F *ᵥ fun n => b n.val) m‖ ^ 2) =
      ∑ m ∈ U, ‖quadraticSieveSum N b m‖ ^ 2 := by
    calc
      _ = ∑ m : U, ‖quadraticSieveSum N b m.val‖ ^ 2 := by simp_rw [hpoint]
      _ = _ := Finset.sum_coe_sort U (fun m : ℕ => ‖quadraticSieveSum N b m‖ ^ 2)
  have hright : (∑ n : V, ‖b n.val‖ ^ 2) = quadraticSieveEnergy N b :=
    Finset.sum_coe_sort V (fun n : ℕ => ‖b n‖ ^ 2)
  rw [hleft, hright] at hb
  exact hb

end Ostmann

end OAI
