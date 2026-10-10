import OAI.NumberTheory.Ostmann.Characters.PivotEliminationBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pivot_fiber_mean_range {α β : Type*} [Fintype α]
    (μ : FinitePrior α) (p : α→β) (R : Finset β) (F : β→ℝ)
    (hR : ∀x,μ.mass x≠0→p x∈R) :
    μ.mean (fun x=>F (p x)) = ∑q∈R,(∑x:α with p x=q,μ.mass x)*F q := by
  classical
  unfold FinitePrior.mean
  symm
  simp_rw [Finset.sum_mul,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hm : μ.mass x=0
  · simp [hm]
  · simp [eq_comm,hR x hm]

theorem dependent_pivot_elimination_range {α β γ : Type*}
    [Fintype α] [Fintype γ] (τ : β→Type*) [∀q,Fintype (τ q)]
    (μ : FinitePrior α) (ν : FinitePrior γ) (p : α→β) (R : Finset β)
    (G : (x:α)→γ→τ (p x)→ℂ) (B : γ→(q:β)→τ q→ℂ) (D : ℝ)
    (hR : ∀x,μ.mass x≠0→p x∈R)
    (hG : ∀x y u,‖G x y u‖≤1)
    (hfiber : ∀q∈R,(∑x:α with p x=q,μ.mass x)*(Fintype.card (τ q):ℝ)≤D) :
    ‖ν.cmean (fun y=>μ.cmean (fun x=>∑u,G x y u*B y (p x) u))‖^2 ≤
      D*ν.mean (fun y=>∑q∈R,∑u,‖B y q u‖^2) := by
  classical
  calc
    _ ≤ ν.mean (fun y=>‖μ.cmean (fun x=>∑u,G x y u*B y (p x) u)‖^2) :=
      ν.norm_cmean_sq_le _
    _ ≤ ν.mean (fun y=>D*∑q∈R,∑u,‖B y q u‖^2) := by
      apply ν.mean_mono
      intro y
      apply (dependent_pivot_row τ μ p (fun x=>G x y) (B y) (fun x=>hG x y)).trans
      rw [pivot_fiber_mean_range μ p R (fun q=>(Fintype.card (τ q):ℝ)*∑u,‖B y q u‖^2) hR,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hfiber q hq) (Finset.sum_nonneg fun _ _=>sq_nonneg _)
    _ = _ := by
      change (∑y,ν.mass y*(D*∑q∈R,∑u,‖B y q u‖^2)) =
        D*(∑y,ν.mass y*(∑q∈R,∑u,‖B y q u‖^2))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring

end Ostmann.Characters

end

end OAI
