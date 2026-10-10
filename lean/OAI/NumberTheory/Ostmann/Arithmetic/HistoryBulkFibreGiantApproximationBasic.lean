import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceScalar
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction HistoryBulkReferencePeriodicMeanSource
open HistorySignedResidueFactorization

theorem norm_oldCompensation {l : ℕ} (h k : History l) :
    ‖oldCompensation h k‖ =
      (h.compensationProduct:ℝ)*(k.compensationProduct:ℝ) := by
  simp only [oldCompensation,norm_mul,Complex.norm_natCast]

theorem norm_staticPairMask_le {l : ℕ} (h k : History l) (outside : List ℕ) :
    ‖staticPairMask h k outside‖ ≤ 1 := by
  classical
  unfold staticPairMask guardIndicator
  split_ifs <;> norm_num

theorem masked_cmean_approximation {α : Type*} [Fintype α]
    (μ : FinitePrior α) {l : ℕ} (h k : History l)
    (good : α→Prop) (periodic main : α→ℂ) (error : ℝ)
    (herror : 0≤error)
    (hpoint : ∀x, μ.mass x≠0 → good x → ‖periodic x-main x‖≤error) :
    ‖μ.cmean (fun x=>guardIndicator (good x)*oldCompensation h k*periodic x)-
      oldCompensation h k*μ.cmean (fun x=>guardIndicator (good x)*main x)‖ ≤
        ((h.compensationProduct:ℝ)*(k.compensationProduct:ℝ))*error := by
  classical
  rw [←FinitePrior.cmean_mul_left, GiantCollisionError.cmean_sub_eq]
  apply GiantCollisionError.norm_cmean_le_of_mass_ne_zero
  intro x hx
  by_cases hg : good x
  · simp only [guardIndicator,hg,ite_true,one_mul]
    rw [←mul_sub,norm_mul,norm_oldCompensation]
    exact mul_le_mul_of_nonneg_left (hpoint x hx hg) (by positivity)
  · simp only [guardIndicator,hg,ite_false,zero_mul,mul_zero,sub_self,norm_zero]
    positivity

theorem cmean_approximation_of_source_identity {α : Type*} [Fintype α]
    (μ : FinitePrior α) {l : ℕ} (h k : History l)
    (good : α→Prop) (source periodic main : α→ℂ) (error : ℝ)
    (herror : 0≤error)
    (hsource : ∀x,μ.mass x≠0 →
      source x=guardIndicator (good x)*oldCompensation h k*periodic x)
    (hpoint : ∀x,μ.mass x≠0 → good x → ‖periodic x-main x‖≤error) :
    ‖μ.cmean source-
      oldCompensation h k*μ.cmean (fun x=>guardIndicator (good x)*main x)‖ ≤
        ((h.compensationProduct:ℝ)*(k.compensationProduct:ℝ))*error := by
  have heq : μ.cmean source = μ.cmean
      (fun x=>guardIndicator (good x)*oldCompensation h k*periodic x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : μ.mass x=0
    · simp only [hx,Complex.ofReal_zero,zero_mul]
    · rw [hsource x hx]
  rw [heq]
  exact masked_cmean_approximation μ h k good periodic main error herror hpoint

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
