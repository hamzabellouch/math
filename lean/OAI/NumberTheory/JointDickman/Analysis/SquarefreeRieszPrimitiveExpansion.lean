import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszExpansion
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszPrimitive
import OAI.NumberTheory.JointDickman.Analysis.RieszLogPolynomial

namespace OAI

/-! # Expansion of the positive Riesz primitive -/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

theorem rieszLogPolynomial_eq (b : ℕ → ℝ) (z : ℝ) (K : ℕ) (x : ℝ) :
    rieszLogPolynomial b z K x = x^2*∑ j ∈ range (K+1), b j*(Real.log x)^(z-1-j) := by
  rw [rieszLogPolynomial,mul_sum]
  apply sum_congr rfl
  intro j _
  unfold logRieszMonomial
  ring

theorem squarefreeRieszPrimitive_expansion {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ b : ℕ → ℝ, b 0 = squarefreeLeadingConstant z/2 ∧ 0 < b 0 ∧
      ∀ K : ℕ, (fun x : ℝ => squarefreeRieszPrimitive z x-rieszLogPolynomial b z K x)
        =O[atTop] (fun x => x^2*(Real.log x)^(z-2-K)) := by
  obtain ⟨b,hb,hb0,h⟩ := squarefreeRieszSum_expansion hz hz1
  refine ⟨b,hb,hb0,fun K => ?_⟩
  have hk := (isBigO_refl (fun x : ℝ => x) atTop).mul (h K)
  apply hk.congr
  · intro x
    rw [squarefreeRieszPrimitive,rieszLogPolynomial_eq]
    ring
  · intro x
    ring

end JointDickman

end OAI
