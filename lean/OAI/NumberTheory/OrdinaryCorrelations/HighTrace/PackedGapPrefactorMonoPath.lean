import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DensitySizeLeTestSize
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GoodGapTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PackedGapPrefactor
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorPathFilling

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.NumericalSubtrees Finset Classical Filter
noncomputable section
namespace NumericalLine

lemma packedGapPrefactor_mono_path (S : PrimeSystem) (ℓ K L J t : ℕ) (hKL : K≤L) :
    packedGapPrefactor S ℓ K J t ≤ packedGapPrefactor S ℓ L J t := by
  unfold packedGapPrefactor gapTemplateBudget
  have hbase : 1 ≤ 2*ℓ+1 := by omega
  gcongr
  positivity [A_pos]

lemma densitySize_le_testSize (B C₀ : ℝ) (h ℓ K L : ℕ) (hKL : K≤L) :
    Specification.densitySize B C₀ h K ≤ PrivateFamily.testSize B C₀ h ℓ L := by
  apply Real.log_le_log (by positivity)
  gcongr
  exact_mod_cast (show K ≤ ℓ+L+L by omega)

theorem source_near_corrupt_small (h : ℕ) (τ T C₀ : ℝ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T) (K : ℕ),K≤pathLength B →
      nearCorruptSum D h (sourceLength B) (pathLength B) K (listCutoff B) cut ≤
        Real.exp (-B^(1+epsilon/2)) := by
  filter_upwards [source_packed_gap_prefactor_small C₀ hC₀,
    source_witness_delta_saving C₀ h hC₀,
    eventually_const_mul_rpow_le (1+epsilon/2) (1+3*epsilon) 4 (by norm_num [epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hpref hdelta hdom hB
  intro D cut K hKL
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hP : 0<sourceMinPrime B := Real.exp_pos _
  have hb := nearCorruptSum_bound (D:=D) (h:=h) (ℓ:=sourceLength B) (L:=pathLength B) (K:=K) (t:=listCutoff B)
    cut (sourceMinPrime B) hP hB0.le (fun p => ⟨(source_prime_lower B hB p).le,source_prime_upper B hB p⟩)
  have hp : packedGapPrefactor (sourceSystem B) (sourceLength B) K ⌈C₀*Real.log B⌉₊ (listCutoff B) ≤
      Real.exp (B^(1+epsilon/2)) :=
    (packedGapPrefactor_mono_path _ _ _ _ _ _ hKL).trans hpref
  have hδ : max (Specification.densitySize B C₀ h K/(sourceMinPrime B*Real.log 2)) ((2+B)/sourceMinPrime B) ≤
      Real.exp (-(1/2)*B^(1-epsilon)) := by
    apply le_trans _ hdelta
    unfold sourceWitnessDelta
    apply max_le_max _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact densitySize_le_testSize B C₀ h (sourceLength B) K (pathLength B) hKL
  have ht : B^(4*epsilon) ≤ (listCutoff B:ℝ) := Nat.le_ceil _
  have hs : (1/2)*B^(1+3*epsilon) ≤ (listCutoff B:ℝ)*((1/2)*B^(1-epsilon)) := by
    have hm := mul_le_mul_of_nonneg_right ht (show 0 ≤ (1/2)*B^(1-epsilon) by positivity)
    have he : B^(4*epsilon)*((1/2)*B^(1-epsilon))=(1/2)*B^(1+3*epsilon) := by
      rw [mul_left_comm,←Real.rpow_add hB0]
      congr 2
      ring
    rwa [he] at hm
  apply hb.trans
  have hδ0 : 0 ≤ max (Specification.densitySize B C₀ h K/(sourceMinPrime B*Real.log 2)) ((2+B)/sourceMinPrime B) :=
    le_trans (by positivity : 0≤(2+B)/sourceMinPrime B) (le_max_right _ _)
  apply (mul_le_mul hp (pow_le_pow_left₀ hδ0 hδ _) (pow_nonneg hδ0 _) (Real.exp_pos _).le).trans
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

def corruptPathLength (B : ℝ) : ℕ := ⌊B^(1-3*rho)⌋₊
lemma corruptPathLength_le (B : ℝ) (hB : 1≤B) : corruptPathLength B ≤ pathLength B := by
  apply Nat.floor_mono
  apply Real.rpow_le_rpow_of_exponent_le hB
  norm_num [rho]

lemma source_near_corrupt_threshold (C₀ : ℝ) (hC₀ : 0≤C₀) :
    ∀ᶠ B : ℝ in atTop,
      (((2*(corruptPathLength B*⌈C₀*Real.log B⌉₊)+1)*listCutoff B:ℕ):ℝ) ≤ (1/2)*B^(1-2*rho) := by
  filter_upwards [eventually_log_ceil_le C₀ (rho/4) hC₀ (by norm_num [rho]),
    eventually_const_mul_rpow_le (1-3*rho+rho/4+4*epsilon) (1-2*rho) 12 (by norm_num [rho,epsilon]),
    eventually_ge_atTop (1:ℝ)] with B hJ hdom hB
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hK : (corruptPathLength B:ℝ) ≤ B^(1-3*rho) := Nat.floor_le (Real.rpow_nonneg hB0.le _)
  have ht : (listCutoff B:ℝ) ≤ 2*B^(4*epsilon) := by
    have he := (Nat.ceil_lt_add_one (Real.rpow_nonneg hB0.le (4*epsilon))).le
    have hone : 1≤B^(4*epsilon) := Real.one_le_rpow hB (by norm_num [epsilon])
    change (⌈B^(4*epsilon)⌉₊:ℝ) ≤ _
    linarith
  have hk1 : 1≤B^(1-3*rho+rho/4) := Real.one_le_rpow hB (by norm_num [rho])
  have hprod : (corruptPathLength B:ℝ)*(⌈C₀*Real.log B⌉₊:ℝ) ≤ B^(1-3*rho+rho/4) := by
    calc
      _ ≤ B^(1-3*rho)*B^(rho/4) := mul_le_mul hK hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hB0.le _)
      _ = _ := (Real.rpow_add hB0 _ _).symm
  have hb : (2*(corruptPathLength B:ℝ)*(⌈C₀*Real.log B⌉₊:ℝ)+1)*(listCutoff B:ℝ) ≤
      6*B^(1-3*rho+rho/4+4*epsilon) := by
    calc
      _ ≤ (3*B^(1-3*rho+rho/4))*(2*B^(4*epsilon)) := by
        apply mul_le_mul (by nlinarith [hprod]) ht (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [mul_mul_mul_comm,←Real.rpow_add hB0]; ring
  push_cast
  nlinarith

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
