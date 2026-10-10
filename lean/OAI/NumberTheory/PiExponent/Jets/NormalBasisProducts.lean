import OAI.NumberTheory.PiExponent.Jets.NormalBasisRigidity
import OAI.NumberTheory.PiExponent.Jets.TransverseWeightedMultiplicity

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisProducts

open scoped BigOperators
open NormalBasisRigidity TransverseWeightedMultiplicity

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def enumeration (A B : Finset ι) (hcard : A.card = B.card) : Fin A.card → ι :=
  fun i => (B.equivFin.symm (Fin.cast hcard i)).val

theorem enumeration_linearIndependent {v : ι → V} (A B : Finset ι)
    (hcard : A.card = B.card) (hB : IsNormalBasis (K := K) v B) :
    LinearIndependent K (fun i => v (enumeration A B hcard i)) := by
  have hli : LinearIndependent K (fun i : B => v i) := hB.1
  exact hli.comp (fun i => B.equivFin.symm (Fin.cast hcard i))
    (B.equivFin.symm.injective.comp (Fin.cast_injective hcard))

theorem prod_equivFin {M : Type*} [CommMonoid M] (A : Finset ι) (f : ι → M) :
    (∏ i : Fin A.card, f (A.equivFin.symm i)) = ∏ i ∈ A, f i := by
  calc
    _ = ∏ i : A, f i := Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort A f

theorem prod_enumeration {M : Type*} [CommMonoid M]
    (A B : Finset ι) (hcard : A.card = B.card) (f : ι → M) :
    (∏ i : Fin A.card, f (enumeration A B hcard i)) = ∏ i ∈ B, f i := by
  calc
    _ = ∏ i : Fin B.card, f (B.equivFin.symm i) :=
      Fintype.prod_equiv (finCongr hcard) _ _ (fun _ => rfl)
    _ = _ := prod_equivFin B f

theorem eventually_uniform_cutoff (n : ℕ)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ k : ℕ, 0 < k → k ≤ n →
      ∀ B : Fin k → Fin n, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i := by
  have ht : Filter.Tendsto (fun N : ℝ => epsilon * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hepsilon
  have hb : ∀ᶠ N : ℝ in Filter.atTop, ∀ j : Fin n,
      (n : ℝ) * cost j < epsilon * N :=
    Filter.eventually_all.mpr (fun j =>
      ht.eventually (Filter.eventually_gt_atTop ((n : ℝ) * cost j)))
  filter_upwards [hb] with N hN
  intro k hk hkn B i
  have hdim : (k : ℝ) ≤ n := by exact_mod_cast hkn
  apply two_le_rectangularCutoff hk (fun j => cost (B j)) (fun j => hcost _) i
  exact (mul_le_mul_of_nonneg_right hdim (hcost _).le).trans_lt (hN (B i))

theorem rectangular_factor_le_constant (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m + 2) :
    (k : ℝ) ^ k * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hdim : (k : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hkm
  have hp : (k : ℝ) ^ k ≤ ((m : ℝ) + 2) ^ (m + 2) := by
    calc
      _ ≤ ((m : ℝ) + 2) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg k) hdim k
      _ ≤ _ := pow_le_pow_right₀ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith) hkm
  have hfactor : (k : ℝ) ^ k ≤ 2 * ((m : ℝ) + 2) ^ (m + 2) := hp.trans (by
    have h : 0 ≤ ((m : ℝ) + 2) ^ (m + 2) := by positivity
    linarith)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase) hkm
  exact mul_le_mul hfactor hpow (pow_nonneg hbase _) (by positivity)

theorem rectangular_comparison_le_constant {m k : ℕ}
    (hkm : k ≤ m + 2) (kappa : Fin k → ℝ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkappa : ∀ i, 0 ≤ kappa i) :
    (k : ℝ) ^ k * (∏ i, kappa i) / (sigma / ((m : ℝ) + 2)) ^ k ≤
      (2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)) * ∏ i, kappa i := by
  have h := rectangular_factor_le_constant m k sigma hsigma hkm
  have hp : 0 ≤ ∏ i, kappa i := Finset.prod_nonneg (fun i _ => hkappa i)
  have hh := mul_le_mul_of_nonneg_right h hp
  convert hh using 1
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
  ring

end PiExponent.NormalBasisProducts
end

end OAI
