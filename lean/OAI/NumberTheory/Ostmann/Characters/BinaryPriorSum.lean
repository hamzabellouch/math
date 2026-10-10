import OAI.NumberTheory.Ostmann.Characters.BinaryPriorSupport

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.BinaryPriorExposure
open Construction BinaryHaar

theorem mean_sum {α β:Type*} [Fintype α] [Fintype β]
    (μ:List Bool→FinitePrior α) (j:ℕ) (p:List Bool) (F:β→Leaves α j→ℝ) :
    mean μ j p (fun x=>∑i,F i x)=∑i,mean μ j p (F i) := by
  induction j generalizing p with
  | zero =>
    change (∑x,(μ p).mass x*∑i,F i x)=∑i,∑x,(μ p).mass x*F i x
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  | succ j ih =>
    change mean μ j (false::p) (fun x=>mean μ j (true::p) (fun y=>∑i,F i (x,y)))=_
    simp_rw [ih]
    rfl

theorem outer_mean_le {α:Type*} [Fintype α] (μ:FinitePrior α) (F:α→ℝ) (B:ℝ)
    (hF:∀x,F x≤B) : μ.mean F≤B := by
  calc
    _ ≤ μ.mean (fun _=>B) := μ.mean_mono hF
    _ = B := by simp only [FinitePrior.mean,← Finset.sum_mul,μ.mass_total,one_mul]

end Ostmann.Characters.BinaryPriorExposure

end

end OAI
