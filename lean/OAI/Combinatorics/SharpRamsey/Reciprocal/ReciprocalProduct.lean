import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalBands
import OAI.Combinatorics.SharpRamsey.Trees.ChronologicalOrder

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real ReciprocalBands
open scoped Classical BigOperators
noncomputable section

lemma reciprocal_window_product (q : ℝ) (r : ℕ) (hq : 0<q)
    (P κ u v gap b : ℝ) (hP : 1≤P) (huv : u-v≤gap)
    (hb : gap+2*κ+log 4≤b) :
    q^r*exp (-b)≤(P*exp ((r:ℝ)*log q-u)*exp (-κ)/2)*
      (P*exp v*exp (-κ)/2) := by
  have he : (P*exp ((r:ℝ)*log q-u)*exp (-κ)/2)*
      (P*exp v*exp (-κ)/2)=P^2*q^r*exp (v-u-2*κ-log 4) := by
    rw [exp_sub (v-u-2*κ) (log 4),exp_log (by norm_num : (0:ℝ)<4)]
    have hx : exp (v-u-2*κ)=exp (v-u)*exp (-κ)*exp (-κ) := by
      rw [←exp_add,←exp_add]
      congr 1
      ring
    rw [hx,exp_sub,exp_sub,exp_nat_mul,exp_log hq]
    ring
  rw [he]
  have hb' : -b≤v-u-2*κ-log 4 := by linarith
  have hp : (1:ℝ)≤P^2 := by nlinarith
  calc
    _ ≤ q^r*exp (v-u-2*κ-log 4) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr hb') (pow_nonneg hq.le _)
    _ = (1:ℝ)*q^r*exp (v-u-2*κ-log 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (pow_nonneg hq.le _)) (exp_pos _).le

lemma integer_window_difference {r : ℕ} {σ gap u v : ℝ}
    (hu : IntegerBand r σ gap u) (hv : IntegerBand r σ gap v) : u-v≤2*gap := by
  rw [IntegerBand,abs_le] at hu hv
  linarith

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype ι] [DecidableEq ι]

theorem chronological_order_of_good_event {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (ι→Projectivization K (Module.Dual K V)×Projectivization K V))
    (i j : ι) (P κ u v L ε z : ℝ) (hP : 1≤P)
    (A : AuxiliarySupport (p.marginal i).fst
      (univ.filter (goodFirst (p.marginal i) (P*exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)) L κ ε))
      (P*exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)) κ)
    (B : AuxiliarySupport (p.marginal j).snd
      (univ.filter (goodSecond (p.marginal j) (P*exp v) L κ ε)) (P*exp v) κ)
    (hevent : ((p.marginal i).fst.prod (p.marginal j).snd).event (univ.filter (fun ay=>
      goodFirst (p.marginal i) (P*exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)) L κ ε ay.1 ∧
      goodSecond (p.marginal j) (P*exp v) L κ ε ay.2 ∧ ay.1.rep ay.2.rep=0))≤z)
    (hz : (4*exp 1)^2*z≤1/(4*(Nat.card K:ℝ))) :
    v≤u+2*κ+log 64 := by
  apply auxiliary_chronological_order hdim (p.marginal i).fst (p.marginal j).snd _ _
    _ _ κ u v (mul_pos (by linarith) (exp_pos _))
    (mul_pos (by linarith) (exp_pos _))
    (by simpa using mul_le_mul_of_nonneg_right hP (exp_pos (((n+3:ℕ):ℝ)*log (Nat.card K)-u)).le)
    (by simpa using mul_le_mul_of_nonneg_right hP (exp_pos v).le) A B
  exact (auxiliary_three_estimates p i j _ _ L κ ε z A B hevent).1.trans hz

end
end SharpLogRamsey.Selection

end

end OAI
