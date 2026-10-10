import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionErrorInteger

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.GiantCollisionError
open Construction

theorem cmean_sub_eq {α : Type*} [Fintype α] (μ : FinitePrior α) (f g : α → ℂ) :
    μ.cmean f-μ.cmean g=μ.cmean (fun x => f x-g x) := by
  simp only [FinitePrior.cmean,mul_sub,Finset.sum_sub_distrib]

theorem norm_cmean_le_of_mass_ne_zero {α : Type*} [Fintype α]
    (μ : FinitePrior α) (f : α → ℂ) (A : ℝ)
    (hf : ∀ x, μ.mass x ≠ 0 → ‖f x‖ ≤ A) : ‖μ.cmean f‖ ≤ A := by
  refine (μ.norm_cmean_le f).trans ?_
  calc
    μ.mean (fun x => ‖f x‖) ≤ μ.mean (fun _ => A) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : μ.mass x=0
      · simp only [hx,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hf x hx) (μ.mass_nonneg x)
    _ = A := μ.mean_const A

theorem pair_mean_fst {α β : Type*} [Fintype α] [Fintype β]
    (μ : FinitePrior α) (ν : FinitePrior β) (h : α → ℝ) :
    (μ.pair ν).mean (fun x => h x.1)=μ.mean h := by
  simp only [FinitePrior.mean,FinitePrior.pair,Fintype.sum_prod_type]
  simp_rw [show ∀ x y, μ.mass x*ν.mass y*h x=μ.mass x*h x*ν.mass y by intros; ring]
  simp only [← Finset.mul_sum,ν.mass_total,mul_one]

theorem logCell_guard_error_with_outer {α : Type*} [Fintype α]
    (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E) (ν : FinitePrior α)
    (f g : (LogCellSample G E × LogCellSample G E) × α → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ x, Nat.Coprime x.1.1.val x.1.2.val → f x=g x)
    (hbound : ∀ x, ¬ Nat.Coprime x.1.1.val x.1.2.val → ‖f x-g x‖ ≤ A) :
    ‖(((logCellPrior G E hZ).pair (logCellPrior G E hZ)).pair ν).cmean f-
      (((logCellPrior G E hZ).pair (logCellPrior G E hZ)).pair ν).cmean g‖ ≤
      A*(Real.exp (1-G)/logCellMass G E) := by
  have h := cmean_error_of_agree_off
    (((logCellPrior G E hZ).pair (logCellPrior G E hZ)).pair ν)
    (fun x => ¬ Nat.Coprime x.1.1.val x.1.2.val) f g A
    (fun x hx => heq x (not_not.mp hx)) hbound
  have hprob := pair_mean_fst ((logCellPrior G E hZ).pair (logCellPrior G E hZ)) ν
    (fun x => if ¬ Nat.Coprime x.1.val x.2.val then (1:ℝ) else 0)
  rw [hprob] at h
  exact h.trans (mul_le_mul_of_nonneg_left (logCell_collision_mass_le G E hZ) hA)

theorem integer_guard_error_averaged {α : Type*} [Fintype α] (μ : FinitePrior α)
    (q : α → ℕ) (G : ℝ) (hq : ∀ x, Nat.Prime (q x))
    (hlog : ∀ x, μ.mass x ≠ 0 → |Real.log (q x)-G| ≤ 1)
    (f g : α → ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ x, μ.mass x ≠ 0 → ∀ n ∈ integerPivotCell G,
      Nat.Coprime n (q x) → f x n=g x n)
    (hbound : ∀ x, μ.mass x ≠ 0 → ∀ n ∈ integerPivotCell G,
      ¬ Nat.Coprime n (q x) → ‖f x n-g x n‖ ≤ A) :
    ‖μ.cmean (fun x => ∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*f x n)-
      μ.cmean (fun x => ∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*g x n)‖ ≤
      A*(8*Real.exp (-G)) := by
  rw [cmean_sub_eq]
  apply norm_cmean_le_of_mass_ne_zero
  intro x hx
  exact integerPivotCell_guard_error G (q x) (hq x) (hlog x hx) (f x) (g x)
    hA (heq x hx) (hbound x hx)

theorem logCell_integer_guard_error (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (f g : LogCellSample G E → ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ q, (logCellPrior G E hZ).mass q ≠ 0 → ∀ n ∈ integerPivotCell G,
      Nat.Coprime n q.val → f q n=g q n)
    (hbound : ∀ q, (logCellPrior G E hZ).mass q ≠ 0 → ∀ n ∈ integerPivotCell G,
      ¬ Nat.Coprime n q.val → ‖f q n-g q n‖ ≤ A) :
    ‖(logCellPrior G E hZ).cmean
        (fun q => ∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*f q n)-
      (logCellPrior G E hZ).cmean
        (fun q => ∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*g q n)‖ ≤
      A*(8*Real.exp (-G)) := by
  apply integer_guard_error_averaged (logCellPrior G E hZ) (fun q => q.val) G
    (fun q => logCellSample_prime q) _ f g hA heq hbound
  intro q hq
  exact (logCellPrimeSource_log_support G E hZ q hq).le

theorem cellSupport_guard_error (N : ℕ) (lo hi G : ℝ) (hhi : hi ≤ G+1)
    (q : ℕ) (hq : Nat.Prime q) (hlog : |Real.log q-G| ≤ 1)
    (f g : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ n ∈ IntegerCell.cellSupport N lo hi, Nat.Coprime n q → f n=g n)
    (hbound : ∀ n ∈ IntegerCell.cellSupport N lo hi,
      ¬ Nat.Coprime n q → ‖f n-g n‖ ≤ A) :
    ‖(∑ n ∈ IntegerCell.cellSupport N lo hi,(externalPivotWeight G n:ℂ)*f n)-
      ∑ n ∈ IntegerCell.cellSupport N lo hi,(externalPivotWeight G n:ℂ)*g n‖ ≤
      A*(8*Real.exp (-G)) := by
  exact (weighted_error_of_agree_off (IntegerCell.cellSupport N lo hi) (externalPivotWeight G)
    (fun n => ¬ Nat.Coprime n q) f g A (fun n _ => externalPivotWeight_nonneg G n)
    (fun n hn hc => heq n hn (not_not.mp hc)) hbound).trans
      (mul_le_mul_of_nonneg_left (cellSupport_collision_mass_le N lo hi G hhi q hq hlog) hA)

end Ostmann.Arithmetic.GiantCollisionError

end

end OAI
