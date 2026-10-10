import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.GiantCollisionError
open Construction

theorem weighted_error_of_agree_off {α : Type*} (s : Finset α)
    (w : α → ℝ) (Bad : α → Prop) [DecidablePred Bad] (f g : α → ℂ) (A : ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x)
    (heq : ∀ x ∈ s, ¬ Bad x → f x = g x)
    (hbound : ∀ x ∈ s, Bad x → ‖f x-g x‖ ≤ A) :
    ‖(∑ x ∈ s, (w x : ℂ)*f x) - ∑ x ∈ s, (w x : ℂ)*g x‖ ≤
      A * ∑ x ∈ s, if Bad x then w x else 0 := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ s, ‖(w x : ℂ)*f x-(w x : ℂ)*g x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, A*(if Bad x then w x else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hb : Bad x
      · rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (hw x hx),ite_eq_left hb]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound x hx hb) (hw x hx)
      · simp only [heq x hx hb,sub_self,norm_zero,ite_eq_right hb,mul_zero,le_refl]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem cmean_error_of_agree_off {α : Type*} [Fintype α] (μ : FinitePrior α)
    (Bad : α → Prop) [DecidablePred Bad] (f g : α → ℂ) (A : ℝ)
    (heq : ∀ x, ¬ Bad x → f x = g x)
    (hbound : ∀ x, Bad x → ‖f x-g x‖ ≤ A) :
    ‖μ.cmean f-μ.cmean g‖ ≤ A*μ.mean (fun x => if Bad x then 1 else 0) := by
  have h := weighted_error_of_agree_off Finset.univ μ.mass Bad f g A
    (fun x _ => μ.mass_nonneg x) (fun x _ => heq x) (fun x _ => hbound x)
  simpa only [FinitePrior.cmean,FinitePrior.mean,mul_ite,mul_one,mul_zero] using h

theorem equality_mass_le {α : Type*} [Fintype α] [DecidableEq α] (μ ν : FinitePrior α)
    (B : ℝ) (hB : ∀ x, ν.mass x ≤ B) :
    (μ.pair ν).mean (fun x => if x.1=x.2 then 1 else 0) ≤ B := by
  change (∑ x : α×α, μ.mass x.1*ν.mass x.2*(if x.1=x.2 then 1 else 0)) ≤ B
  rw [Fintype.sum_prod_type]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  calc
    ∑ x, μ.mass x*ν.mass x ≤ ∑ x, μ.mass x*B :=
      Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hB x) (μ.mass_nonneg x)
    _ = B := by rw [← Finset.sum_mul,μ.mass_total,one_mul]

theorem primeSource_not_coprime_iff_eq (S : PrimeSource) (p q : S.Sample) :
    ¬ Nat.Coprime p.val q.val ↔ p=q := by
  rw [Nat.coprime_primes (S.prime p.val p.property) (S.prime q.val q.property)]
  exact not_not.trans Subtype.ext_iff.symm

theorem primeSource_collision_mass_le (S : PrimeSource) (B : ℝ)
    (hB : ∀ p, S.law.mass p ≤ B) :
    (S.law.pair S.law).mean (fun x => if ¬ Nat.Coprime x.1.val x.2.val then 1 else 0) ≤ B := by
  simpa only [primeSource_not_coprime_iff_eq] using equality_mass_le S.law S.law B hB

theorem logCellPrior_mass_le_exp (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (p : LogCellSample G E) :
    (logCellPrior G E hZ).mass p ≤ Real.exp (1-G)/logCellMass G E := by
  change logCellWeight G p/(∑ q : LogCellSample G E,logCellWeight G q) ≤ _
  rw [logCell_sample_sum]
  exact div_le_div_of_nonneg_right (logCellWeight_le_exp G p) hZ.le

theorem logCell_collision_mass_le (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E) :
    ((logCellPrior G E hZ).pair (logCellPrior G E hZ)).mean
      (fun x => if ¬ Nat.Coprime x.1.val x.2.val then 1 else 0) ≤
      Real.exp (1-G)/logCellMass G E :=
  primeSource_collision_mass_le (logCellPrimeSource G E hZ) _ (logCellPrior_mass_le_exp G E hZ)

theorem logCell_guard_error (G : ℝ) (E : Finset ℕ) (hZ : 0 < logCellMass G E)
    (f g : LogCellSample G E × LogCellSample G E → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ x, Nat.Coprime x.1.val x.2.val → f x=g x)
    (hbound : ∀ x, ¬ Nat.Coprime x.1.val x.2.val → ‖f x-g x‖ ≤ A) :
    ‖((logCellPrior G E hZ).pair (logCellPrior G E hZ)).cmean f -
      ((logCellPrior G E hZ).pair (logCellPrior G E hZ)).cmean g‖ ≤
      A*(Real.exp (1-G)/logCellMass G E) := by
  exact (cmean_error_of_agree_off _ (fun x => ¬ Nat.Coprime x.1.val x.2.val) f g A
    (fun x hx => heq x (not_not.mp hx)) hbound).trans
      (mul_le_mul_of_nonneg_left (logCell_collision_mass_le G E hZ) hA)

end Ostmann.Arithmetic.GiantCollisionError

end

end OAI
