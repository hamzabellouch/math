import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset

namespace OrdinaryCorrelations.SourceSieveEulerProduct

def reciprocalHom : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_inv_rev,mul_comm]

lemma reciprocal_prime_norm {p : ℕ} (hp : p.Prime) : ‖reciprocalHom p‖ < 1 := by
  have hpR : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  change ‖(p:ℝ)⁻¹‖ < 1
  rw [norm_inv,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg p)]
  exact (inv_lt_one₀ (by linarith)).mpr hpR

lemma harmonic_le_finite_euler (N : ℕ) :
    (harmonic N:ℝ) ≤ ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹)⁻¹ := by
  let s := (N+1).primesBelow
  have ht := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalHom) (fun hp => reciprocal_prime_norm hp) s).2
  have hfil : s.filter Nat.Prime = s := Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primesBelow hp)
  simp only [hfil] at ht
  have hs (n : ↥(Finset.Icc 1 N)) : n.val ∈ Nat.factoredNumbers s := by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpn
    apply Nat.mem_primesBelow.mpr
    refine ⟨?_,hp⟩
    have hn := Finset.mem_Icc.mp n.property
    exact Nat.lt_succ_of_le ((Nat.le_of_dvd (by omega) hpn).trans hn.2)
  let e : ↥(Finset.Icc 1 N) ↪ Nat.factoredNumbers s :=
    ⟨fun n => ⟨n.val, hs n⟩, fun x y h => Subtype.ext (congrArg (fun n : Nat.factoredNumbers s => n.val) h)⟩
  have hb := ht.summable.sum_le_tsum (Finset.univ.map e)
    (fun n _ => show 0 ≤ reciprocalHom n.val by change 0 ≤ (n.val:ℝ)⁻¹; positivity)
  rw [ht.tsum_eq] at hb
  simp only [Finset.sum_map] at hb
  change (∑ n : ↥(Finset.Icc 1 N), (n.val:ℝ)⁻¹) ≤
    ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹)⁻¹ at hb
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n : ℕ => (n:ℝ)⁻¹)] at hb
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using hb

theorem prime_product_le_log_inv (N : ℕ) (hN : 1 ≤ N) :
    (∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹)) ≤ (Real.log (N+1:ℕ))⁻¹ := by
  have hp (p : ℕ) (hp : p ∈ (N+1).primesBelow) : 0 < 1-(p:ℝ)⁻¹ := by
    have hpR : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hi := (inv_lt_one₀ (show (0:ℝ)<p by linarith)).mpr hpR
    linarith
  have hprod : 0 < ∏ p ∈ (N+1).primesBelow, (1-(p:ℝ)⁻¹) := Finset.prod_pos hp
  have hlog : 0 < Real.log (N+1:ℕ) := Real.log_pos (by exact_mod_cast (show 1 < N+1 by omega))
  have hh := (log_add_one_le_harmonic N).trans (harmonic_le_finite_euler N)
  rw [Finset.prod_inv_distrib] at hh
  have hi := one_div_le_one_div_of_le hlog hh
  simpa only [one_div,inv_inv] using hi

end OrdinaryCorrelations.SourceSieveEulerProduct

end

end OAI
