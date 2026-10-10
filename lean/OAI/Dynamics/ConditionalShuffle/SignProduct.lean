import OAI.Dynamics.ConditionalShuffle.PhysicalRate

namespace OAI

noncomputable section
namespace Thorp.Trim
open scoped Classical
open Thorp.Fourier
variable {α : Type} [Fintype α] [DecidableEq α]

lemma realConv_dirac (a b : Equiv.Perm α) :
    realConv (fun g => if g = a then (1 : ℝ) else 0) (fun g => if g = b then 1 else 0) =
      fun g => if g = a * b then 1 else 0 := by
  funext g
  simp only [realConv, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [inv_mul_eq_iff_eq_mul]

lemma signDichotomy_realConv (μ ν : Equiv.Perm α → ℝ) (hμ : signDichotomy μ)
    (hν : signDichotomy ν) : signDichotomy (realConv μ ν) := by
  rcases hμ with hμ | ⟨a,rfl⟩
  · left
    rw [realConv_character, hμ, zero_mul]
  · rcases hν with hν | ⟨b,rfl⟩
    · left
      rw [realConv_character, hν, mul_zero]
    · right
      exact ⟨a*b, realConv_dirac a b⟩

lemma signDichotomy_realProduct (n : ℕ) (μ : Fin n → Equiv.Perm α → ℝ)
    (hμ : ∀ i, signDichotomy (μ i)) : signDichotomy (realProduct n μ) := by
  induction n with
  | zero => exact Or.inr ⟨1, by funext g; simp [realProduct]⟩
  | succ n ih =>
      exact signDichotomy_realConv _ _ (hμ _) (ih (Fin.init μ) (fun i => hμ i.castSucc))

end Thorp.Trim

end

end OAI
