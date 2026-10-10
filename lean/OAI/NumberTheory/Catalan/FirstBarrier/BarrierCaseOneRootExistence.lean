import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

theorem rationalPolynomial_root_mem_Ioo_of_eval_mul_neg (p : ℚ[X])
    {a b : ℚ} (hab : a < b) (hs : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, x ∈ Set.Ioo (a : ℝ) (b : ℝ) ∧
      (p.map (Rat.castHom ℝ)).eval x = 0 := by
  have heval (q : ℚ) :
      (p.map (Rat.castHom ℝ)).eval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
    change (p.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (p.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hs' : (p.map (Rat.castHom ℝ)).eval (a : ℝ) *
      (p.map (Rat.castHom ℝ)).eval (b : ℝ) < 0 := by
    simp only [heval]
    exact_mod_cast hs
  have hc : ContinuousOn (fun x : ℝ => (p.map (Rat.castHom ℝ)).eval x)
      (Set.Icc (a : ℝ) (b : ℝ)) := (p.map (Rat.castHom ℝ)).continuousOn
  rcases mul_neg_iff.mp hs' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ)) := ⟨hb, ha⟩
    rcases (intermediate_value_Ioo' hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ)) := ⟨ha, hb⟩
    rcases (intermediate_value_Ioo hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩

end InternalCatalan

end

end OAI
