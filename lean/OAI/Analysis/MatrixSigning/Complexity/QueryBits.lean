import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SearchStep
import OAI.Analysis.MatrixSigning.Complexity.BitSupport

namespace OAI

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma Pencil.next_displacement (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hstep : 0 ≤ step) (hmesh : 0 < mesh) :
    ‖realVector (B.next step mesh y)-realVector y‖ ≤
      (step:ℝ)+(n+1)*(mesh:ℝ) := by
  cases hv : B.witness y with
  | none =>
    simp only [Pencil.next,hv,sub_self,norm_zero]
    have hs : (0:ℝ) ≤ step := by exact_mod_cast hstep
    have hm : (0:ℝ) < mesh := by exact_mod_cast hmesh
    positivity
  | some v =>
    let z := fun i => y i-step*B.normal v i/l1 (B.normal v)
    have he := realVector_round_error mesh hmesh z
    have hz : ‖realVector z-realVector y‖ ≤ (step:ℝ) := by
      rw [realVector_step,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (by exact_mod_cast hstep : (0:ℝ) ≤ step)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (normalized_norm_le_one (B.normal v)) (by exact_mod_cast hstep : (0:ℝ) ≤ step)
    calc
      _ ≤ ‖realVector (B.next step mesh y)-realVector z‖+‖realVector z-realVector y‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (n+1)*(mesh:ℝ)+(step:ℝ) := by
        exact add_le_add (by simpa only [Pencil.next,hv] using he) hz
      _ = _ := by ring

lemma Pencil.iterate_uniform_norm (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hstep : 0 ≤ step) (hmesh : 0 < mesh) (k : ℕ) :
    ‖realVector ((B.next step mesh)^[k] y)‖ ≤
      ‖realVector y‖+k*((step:ℝ)+(n+1)*(mesh:ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hd := B.next_displacement step mesh ((B.next step mesh)^[k] y) hstep hmesh
    have ht := norm_le_norm_sub_add (realVector (B.next step mesh ((B.next step mesh)^[k] y)))
      (realVector ((B.next step mesh)^[k] y))
    push_cast
    linarith

theorem Pencil.iterate_uniform_mesh (B : Pencil n m) (step mesh Y : ℚ) (y : Fin n → ℚ)
    (hstep : 0 ≤ step) (hmesh : 0 < mesh) (hy : ‖realVector y‖ ≤ (Y:ℝ))
    (hm : ∀ i, ∃ v : ℤ, y i=mesh*v) (k : ℕ) (i : Fin n) :
    ∃ v : ℤ, ((B.next step mesh)^[k] y) i=mesh*v ∧
      (|v|:ℤ) ≤ ⌈(Y+k*(step+(n+1)*mesh))/mesh⌉ := by
  let z := (B.next step mesh)^[k] y
  obtain ⟨v,hv⟩ := B.iterate_on_mesh step mesh y hm k i
  refine ⟨v,hv,?_⟩
  have hn := B.iterate_uniform_norm step mesh y hstep hmesh k
  have hi := (PiLp.norm_apply_le (realVector z) i).trans hn
  have ha : |z i| ≤ Y+k*(step+(n+1)*mesh) := by
    have hh : |(z i:ℝ)| ≤ (Y:ℝ)+k*((step:ℝ)+(n+1)*(mesh:ℝ)) := by
      have h := hi.trans (add_le_add hy le_rfl)
      simp only [Real.norm_eq_abs] at h
      exact h
    exact_mod_cast hh
  change z i=mesh*v at hv
  rw [hv,abs_mul,abs_of_pos hmesh] at ha
  have hq : (|v|:ℚ) ≤ (Y+k*(step+(n+1)*mesh))/mesh := by
    apply (le_div_iff₀ hmesh).mpr
    simpa only [Int.cast_abs,mul_comm] using ha
  exact_mod_cast hq.trans (Int.le_ceil _)

end CurrentKS.RationalSDP
namespace CurrentKS.RationalBits

lemma Parts.intCast {b : ℕ} {z : ℤ} (hz : z.natAbs ≤ 2^b) : Parts b (z:ℚ) := by
  constructor
  · simpa only [Rat.num_intCast] using hz
  · simpa only [Rat.den_intCast] using Nat.one_le_two_pow

lemma natCast_parts_size (n : ℕ) : Parts n.size (n:ℚ) := by
  constructor
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.lt_size_self n).le
  · simpa only [Rat.den_natCast] using Nat.one_le_two_pow

lemma Parts.abs_le {b : ℕ} {q : ℚ} (hq : Parts b q) : |q| ≤ (2:ℚ)^b := by
  have hnum : |(q.num:ℚ)| ≤ (2:ℚ)^b := by
    have hh : (q.num.natAbs:ℚ) ≤ (2:ℚ)^b := by exact_mod_cast hq.1
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  have hd : (1:ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  rw [←Rat.num_div_den q,abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)]
  apply (div_le_iff₀ (by positivity : (0:ℚ)<q.den)).mpr
  exact hnum.trans (le_mul_of_one_le_right (by positivity) hd)

lemma Parts.ceil {b : ℕ} {q : ℚ} (hq : Parts b q) : Parts (b+1) (⌈q⌉:ℚ) := by
  apply Parts.intCast
  have ha := hq.abs_le
  have hlow : -(2:ℚ)^b ≤ q := (_root_.abs_le.mp ha).1
  have hupp : q ≤ (2:ℚ)^b := (_root_.abs_le.mp ha).2
  have hlo : -(2:ℚ)^b ≤ (⌈q⌉:ℚ) := hlow.trans (Int.le_ceil q)
  have hup : (⌈q⌉:ℚ)<(2:ℚ)^b+1 := by linarith [Int.ceil_lt_add_one q]
  have htwo : (2:ℚ)^b+1 ≤ (2:ℚ)^(b+1) := by
    rw [pow_succ];have hh : (1:ℚ)≤2^b := one_le_pow₀ (by norm_num);linarith
  have hl : -(2:ℚ)^(b+1) ≤ (⌈q⌉:ℚ) := by
    have hb : (2:ℚ)^b ≤ 2^(b+1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ b)
    linarith
  have hh : |(⌈q⌉:ℚ)| ≤ (2:ℚ)^(b+1) := _root_.abs_le.mpr ⟨hl,hup.le.trans htwo⟩
  have hn : ((⌈q⌉:ℤ).natAbs:ℚ) ≤ (2:ℚ)^(b+1) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
  exact_mod_cast hn
end CurrentKS.RationalBits

namespace CurrentKS.RationalSDP
open CurrentKS.RationalBits
open scoped BigOperators

variable {n m : ℕ}

theorem Pencil.iterate_zero_parts (B : Pencil n m) {b : ℕ} (step mesh : ℚ)
    (hstep : 0 ≤ step) (hmesh : 0 < mesh) (hs : Parts b step) (hm : Parts b mesh)
    (k : ℕ) (i : Fin n) :
    Parts (k.size+n.size+4*b+3) (((B.next step mesh)^[k] 0) i) := by
  obtain ⟨v,hv,hbound⟩ := B.iterate_uniform_mesh step mesh 0 0 hstep hmesh (by
      have hz : realVector (0:Fin n → ℚ)=0 := by ext i; simp [realVector]
      rw [hz]; simp)
    (fun _ => ⟨0,by simp⟩) k i
  have hn := (natCast_parts_size n).add parts_one
  have hq := ((natCast_parts_size k).mul (hs.add (hn.mul hm))).div hm
  have he : Parts (k.size+n.size+3*b+2)
      (((k:ℚ)*(step+((n:ℚ)+1)*mesh))/mesh) := by
    convert hq using 1
    ring
  have hc := he.ceil
  have hb : v.natAbs ≤ 2^(k.size+n.size+3*b+2+1) := by
    have hv' : (|v|:ℤ) ≤ |⌈((k:ℚ)*(step+((n:ℚ)+1)*mesh))/mesh⌉| := by
      simpa only [zero_add] using hbound.trans (le_abs_self _)
    have hab : v.natAbs ≤ (⌈((k:ℚ)*(step+((n:ℚ)+1)*mesh))/mesh⌉:ℤ).natAbs := by
      exact_mod_cast (show (v.natAbs:ℤ) ≤ ((⌈((k:ℚ)*(step+((n:ℚ)+1)*mesh))/mesh⌉:ℤ).natAbs:ℤ) by
        simpa only [Int.natCast_natAbs] using hv')
    exact hab.trans (by simpa only [Rat.num_intCast] using hc.1)
  have hh := hm.mul (Parts.intCast hb)
  rw [hv]
  convert hh using 1
  omega
end CurrentKS.RationalSDP

end OAI
