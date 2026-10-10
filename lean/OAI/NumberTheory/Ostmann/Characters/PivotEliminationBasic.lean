import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pivot_fiber_mean {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (p : α→β) (F : β→ℝ) :
    μ.mean (fun x=>F (p x)) = ∑q:β,(∑x:α with p x=q,μ.mass x)*F q := by
  classical
  unfold FinitePrior.mean
  rw [← Finset.sum_fiberwise (Finset.univ:Finset α) p (fun x=>μ.mass x*F (p x))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

theorem dependent_pivot_row {α β : Type*} [Fintype α]
    (τ : β→Type*) [∀q,Fintype (τ q)] (μ : FinitePrior α) (p : α→β)
    (G : (x:α)→τ (p x)→ℂ) (B : (q:β)→τ q→ℂ)
    (hG : ∀x u,‖G x u‖≤1) :
    ‖μ.cmean (fun x=>∑u,G x u*B (p x) u)‖^2 ≤
      μ.mean (fun x=>(Fintype.card (τ (p x)):ℝ)*∑u,‖B (p x) u‖^2) := by
  refine (μ.norm_cmean_sq_le _).trans (μ.mean_mono fun x=>?_)
  apply (row_cauchy (G x) (B (p x))).trans
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _=>sq_nonneg _)
  calc
    (∑u,‖G x u‖^2) ≤ ∑_u:τ (p x),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hG x u) 2
    _ = _ := by simp

theorem dependent_pivot_elimination {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (τ : β→Type*) [∀q,Fintype (τ q)]
    (μ : FinitePrior α) (ν : FinitePrior γ) (p : α→β)
    (G : (x:α)→γ→τ (p x)→ℂ) (B : γ→(q:β)→τ q→ℂ) (D : ℝ)
    (hG : ∀x y u,‖G x y u‖≤1)
    (hfiber : ∀q,(∑x:α with p x=q,μ.mass x)*(Fintype.card (τ q):ℝ)≤D) :
    ‖ν.cmean (fun y=>μ.cmean (fun x=>∑u,G x y u*B y (p x) u))‖^2 ≤
      D*ν.mean (fun y=>∑q:β,∑u,‖B y q u‖^2) := by
  classical
  calc
    _ ≤ ν.mean (fun y=>‖μ.cmean (fun x=>∑u,G x y u*B y (p x) u)‖^2) :=
      ν.norm_cmean_sq_le _
    _ ≤ ν.mean (fun y=>D*∑q:β,∑u,‖B y q u‖^2) := by
      apply ν.mean_mono
      intro y
      apply (dependent_pivot_row τ μ p (fun x=>G x y) (B y) (fun x=>hG x y)).trans
      rw [pivot_fiber_mean μ p (fun q=>(Fintype.card (τ q):ℝ)*∑u,‖B y q u‖^2),Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hfiber q) (Finset.sum_nonneg fun _ _=>sq_nonneg _)
    _ = _ := by
      change (∑y,ν.mass y*(D*∑q:β,∑u,‖B y q u‖^2)) =
        D*(∑y,ν.mass y*(∑q:β,∑u,‖B y q u‖^2))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring

end Ostmann.Characters

end

end OAI
