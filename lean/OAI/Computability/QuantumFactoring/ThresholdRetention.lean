import Mathlib
import OAI.Computability.QuantumFactoring.FactorGuess
import OAI.Computability.QuantumFactoring.RetentionDenominators
import OAI.Computability.QuantumFactoring.RationalRounding
import OAI.Computability.QuantumFactoring.FilterExpressionSyntax

namespace OAI

section
open scoped BigOperators


/-! Exact threshold thinning by a FIXED (not rejection-sampled) block of fair
bits. The complete block is retained in the physical history. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness BooleanNetwork BitArithmetic

def bitsNatEquiv (b : ℕ) : Basis b ≃ Fin (2^b) :=
  (bitsEquiv b).trans BitVec.equivFin.toEquiv

lemma bitsNatEquiv_val (b : ℕ) (x : Basis b) :
    (bitsNatEquiv b x).val=(bitsValue x).toNat := rfl

lemma fair_threshold_mass {b z : ℕ} (hz : z≤2^b) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat<z) (fairState b)=
      (z:ℝ)/2^b := by
  classical
  unfold outcomeMass
  simp only [fairState_mass]
  rw [Fintype.sum_equiv (bitsNatEquiv b)
    (fun x => if (bitsValue x).toNat<z then (2:ℝ)⁻¹^b else 0)
    (fun i => if i.val<z then (2:ℝ)⁻¹^b else 0) (fun _ => rfl)]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i<z then (2:ℝ)⁻¹^b else 0) (2^b)]
  have he : (∑ i ∈ Finset.range (2^b), if i<z then (2:ℝ)⁻¹^b else 0)=
      ∑ i ∈ Finset.range z, (2:ℝ)⁻¹^b := by
    rw [← Finset.sum_subset (Finset.range_mono hz)]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]
    · intro i _ hi
      rw [ite_eq_right (by simpa using hi)]
  rw [he]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,inv_pow,div_eq_mul_inv]

/-- The natural floor implementation of the exact dyadic acceptance threshold. -/
def thresholdExpr {v : Type*} (T : ℕ) (p : RatExpr v) (coin : NatExpr v) : NatExpr v :=
  .iteLe (.add coin (.const 1)) ((p*RatExpr.ofNat (.const (2^T))).floor.toNat)
    (.const 1) (.const 0)

lemma thresholdExpr_eval {v : Type*} (x : v→ℕ) (T : ℕ) (p : RatExpr v) (coin : NatExpr v) :
    (thresholdExpr T p coin).eval x=1 ↔
      coin.eval x<(Int.floor (p.eval x*(2:ℚ)^T)).toNat := by
  simp only [thresholdExpr,NatExpr.eval,IntExpr.eval_toNat,RatExpr.eval_floor,RatExpr.eval_times,
    RatExpr.eval_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  split_ifs with h
  · exact ⟨fun _ => Nat.lt_of_succ_le h,fun _ => rfl⟩
  · exact ⟨False.elim,fun hh => h (Nat.succ_le_of_lt hh)⟩

lemma dyadic_fair_threshold {b : ℕ} {p : ℚ} (h : OrderTrial.DyadicAt b p)
    (h₀ : 0≤p) (h₁ : p≤1) :
    outcomeMass (fun x : Basis b => (bitsValue x).toNat<(Int.floor (p*(2:ℚ)^b)).toNat)
      (fairState b)=(p:ℝ) := by
  obtain ⟨z,hz,hp,hfloor⟩ := OrderTrial.retained_numerator h h₀ h₁
  rw [hfloor,fair_threshold_mass hz,hp]
  push_cast
  rfl

end ExactQuantumFactoring


end

end OAI
