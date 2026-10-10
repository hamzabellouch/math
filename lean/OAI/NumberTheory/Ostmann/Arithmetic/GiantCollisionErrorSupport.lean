import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionError

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.GiantCollisionError
open Construction

theorem weighted_guard_error_support {α : Type*} (s : Finset α)
    (w : α→ℝ) (Good : α→Prop) [DecidablePred Good] (f : α→ℂ)
    {A : ℝ} (hw : ∀x∈s,0≤w x)
    (hf : ∀x∈s,w x≠0→¬Good x→‖f x‖≤A) :
    ‖(∑x∈s,(w x:ℂ)*(if Good x then f x else 0))-
      ∑x∈s,(w x:ℂ)*f x‖≤A*∑x∈s,if ¬Good x then w x else 0 := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑x∈s,‖(w x:ℂ)*(if Good x then f x else 0)-(w x:ℂ)*f x‖ := norm_sum_le _ _
    _ ≤ ∑x∈s,A*(if ¬Good x then w x else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hz : w x=0
      · simp only [hz,Complex.ofReal_zero,zero_mul,sub_self,norm_zero,ite_self,mul_zero,le_refl]
      · by_cases hg : Good x
        · simp [hg]
        · simp only [ite_eq_right hg,ite_eq_left hg,mul_zero,zero_sub,norm_neg,norm_mul,Complex.norm_real,
            Real.norm_eq_abs,abs_of_nonneg (hw x hx)]
          exact (mul_le_mul_of_nonneg_left (hf x hx hz hg) (hw x hx)).trans_eq (mul_comm _ _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem logCell_guard_support (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (f : LogCellSample G E×LogCellSample G E→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀p q,(logCellPrior G E hZ).mass p≠0→(logCellPrior G E hZ).mass q≠0→
      ¬Nat.Coprime p.val q.val→‖f (p,q)‖≤A) :
    ‖((logCellPrior G E hZ).pair (logCellPrior G E hZ)).cmean
        (fun x=>if Nat.Coprime x.1.val x.2.val then f x else 0)-
      ((logCellPrior G E hZ).pair (logCellPrior G E hZ)).cmean f‖≤
      A*(Real.exp (1-G)/logCellMass G E) := by
  let μ := (logCellPrior G E hZ).pair (logCellPrior G E hZ)
  have hh := weighted_guard_error_support Finset.univ μ.mass
    (fun x=>Nat.Coprime x.1.val x.2.val) f (fun x _=>μ.mass_nonneg x) (by
      rintro ⟨p,q⟩ _ hz hb
      exact hf p q (mul_ne_zero_iff.mp hz).1 (mul_ne_zero_iff.mp hz).2 hb)
  have hmass := logCell_collision_mass_le G E hZ
  have hh' : ‖μ.cmean (fun x=>if Nat.Coprime x.1.val x.2.val then f x else 0)-μ.cmean f‖≤
      A*μ.mean (fun x=>if ¬Nat.Coprime x.1.val x.2.val then 1 else 0) := by
    simpa only [FinitePrior.cmean,FinitePrior.mean,mul_ite,mul_one,mul_zero] using hh
  exact hh'.trans (mul_le_mul_of_nonneg_left hmass hA)

theorem integer_guard_support (G : ℝ) (q : ℕ) (hq : q.Prime)
    (hlog : |Real.log q-G|≤1) (f : ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀n∈integerPivotCell G,externalPivotWeight G n≠0→¬Nat.Coprime n q→‖f n‖≤A) :
    ‖(∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*(if Nat.Coprime n q then f n else 0))-
      ∑n∈integerPivotCell G,(externalPivotWeight G n:ℂ)*f n‖≤A*(8*Real.exp (-G)) :=
  (weighted_guard_error_support (integerPivotCell G) (externalPivotWeight G)
    (fun n=>Nat.Coprime n q) f (fun n _=>externalPivotWeight_nonneg G n) hf).trans
      (mul_le_mul_of_nonneg_left (integerPivotCell_collision_mass_le G q hq hlog) hA)

theorem logCell_integer_guard_support (G : ℝ) (E : Finset ℕ) (hZ : 0<logCellMass G E)
    (f : LogCellSample G E→ℕ→ℂ) {A : ℝ} (hA : 0≤A)
    (hf : ∀q,(logCellPrior G E hZ).mass q≠0→∀n∈integerPivotCell G,
      externalPivotWeight G n≠0→¬Nat.Coprime n q.val→‖f q n‖≤A) :
    ‖(logCellPrior G E hZ).cmean (fun q=>∑n∈integerPivotCell G,
        (externalPivotWeight G n:ℂ)*(if Nat.Coprime n q.val then f q n else 0))-
      (logCellPrior G E hZ).cmean (fun q=>∑n∈integerPivotCell G,
        (externalPivotWeight G n:ℂ)*f q n)‖≤A*(8*Real.exp (-G)) := by
  rw [cmean_sub_eq]
  apply norm_cmean_le_of_mass_ne_zero
  intro q hq
  exact integer_guard_support G q.val (logCellSample_prime q)
    (logCellPrimeSource_log_support G E hZ q hq).le (f q) hA (hf q hq)

end Ostmann.Arithmetic.GiantCollisionError

end

end OAI
