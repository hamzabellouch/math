import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceWitnessBasicScales
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecificationSlotCount

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

noncomputable def specificationPrefactor (S : PrimeSystem) (L J : ℕ) : ℝ :=
  (specificationBudget L J:ℝ)*(max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹))^(specificationSlotCount L J)
noncomputable def specificationDegree (L J : ℕ) : ℕ := 2*(specificationSlotCount L J)+L+4
noncomputable def specificationBase (S : PrimeSystem) (L J : ℕ) : ℝ :=
  2+(specificationSlotCount L J:ℝ)+(L:ℝ)+max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)

lemma specification_polynomial_bound (S : PrimeSystem) (L J : ℕ) :
    specificationPrefactor S L J ≤ (specificationBase S L J)^(specificationDegree L J) := by
  let Q := specificationBase S L J
  let N := specificationSlotCount L J
  let H : ℝ := max 1 (∑ p ∈ S.primes,(p:ℝ)⁻¹)
  have hH : 1 ≤ H := le_max_left _ _
  have hQ : 2 ≤ Q := by
    change 2 ≤ 2+(N:ℝ)+(L:ℝ)+H
    linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)),(Nat.cast_nonneg L : (0:ℝ) ≤ (L:ℝ))]
  have hN : (N:ℝ)+1 ≤ Q := by dsimp [N,Q,specificationBase] at *; linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ (L:ℝ))]
  have hL : (L:ℝ)+1 ≤ Q := by dsimp [Q,specificationBase]; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
  have hHQ : H ≤ Q := by
    change H ≤ 2+(N:ℝ)+(L:ℝ)+H
    linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ)),(Nat.cast_nonneg L : (0:ℝ) ≤ (L:ℝ))]
  have hf : (specificationBudget L J:ℝ) =
      ((N:ℝ)+1)*(((L:ℝ)+1)^2*2^L)*((N:ℝ)+1)^N*(N:ℝ) := by
    simp only [specificationBudget,SpecMetadata,Fintype.card_prod,Fintype.card_fin,
      Fintype.card_fun,Fintype.card_bool,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat]
    dsimp only [N]
    ring
  unfold specificationPrefactor
  rw [hf]
  change _ ≤ Q^(2*N+L+4)
  calc
    _ ≤ Q*(Q^2*Q^L)*Q^N*Q*Q^N := by
      apply mul_le_mul
      · apply mul_le_mul
        · apply mul_le_mul
          · apply mul_le_mul
            · exact hN
            · exact mul_le_mul (pow_le_pow_left₀ (by positivity) hL 2)
                (pow_le_pow_left₀ (by norm_num) hQ L) (by positivity) (by positivity)
            · positivity
            · positivity
          · exact pow_le_pow_left₀ (by positivity) hN N
          · positivity
          · positivity
        · exact le_trans (by linarith : (N:ℝ) ≤ (N:ℝ)+1) hN
        · positivity
        · positivity
      · exact pow_le_pow_left₀ (zero_le_one.trans hH) hHQ N
      · positivity
      · positivity
    _ = _ := by simp only [pow_add,pow_mul]; ring

lemma source_specification_scales (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      (specificationDegree (pathLength B) ⌈C₀*Real.log B⌉₊:ℝ) ≤ B^(1-rho/3) ∧
      specificationBase (sourceSystem B) (pathLength B) ⌈C₀*Real.log B⌉₊ ≤ B^2 := by
  filter_upwards [source_witness_basic_scales C₀ hC₀,
    eventually_const_mul_rpow_le (1-rho+epsilon/8) (1-rho/2) 2 (by norm_num [rho,epsilon]),
    eventually_const_mul_rpow_le (1-rho/2) (1-rho/3) 7 (by norm_num [rho]),
    eventually_const_mul_rpow_le 1 2 5 (by norm_num)] with B hs hprod hdeg hbase
  obtain ⟨hB,_,_,_,hJ,hH⟩ := hs
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hL : (pathLength B:ℝ) ≤ B^(1-rho) := Nat.floor_le (Real.rpow_nonneg hB0.le _)
  let R := B^(1-rho/2)
  have hR : 1 ≤ R := Real.one_le_rpow hB (by norm_num [rho])
  have hLR : (pathLength B:ℝ) ≤ R := hL.trans
    (Real.rpow_le_rpow_of_exponent_le hB (by norm_num [rho]))
  have hRB : R ≤ B := Real.rpow_le_self_of_one_le hB (by norm_num [rho])
  have hN : (specificationSlotCount (pathLength B) ⌈C₀*Real.log B⌉₊:ℝ) ≤ R := by
    have hh := mul_le_mul hL hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hB0.le _)
    rw [←Real.rpow_add hB0] at hh
    have h1 : 1 ≤ B^(1-rho+epsilon/8) := Real.one_le_rpow hB (by norm_num [rho,epsilon])
    apply le_trans _ hprod
    simp only [specificationSlotCount,SpecCodeSlot,Fintype.card_option,Fintype.card_prod,Fintype.card_fin,
      Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    linarith
  constructor
  · apply le_trans _ hdeg
    simp only [specificationDegree,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    linarith
  · apply le_trans _ (by simpa only [Real.rpow_one,Real.rpow_two] using hbase)
    unfold specificationBase
    linarith

lemma source_specification_prefactor (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      specificationPrefactor (sourceSystem B) (pathLength B) ⌈C₀*Real.log B⌉₊ ≤
        Real.exp (B^(1-rho/4)) := by
  have hh := (isLittleO_log_rpow_atTop (by norm_num [rho] : 0 < rho/12)).tendsto_div_nhds_zero
  filter_upwards [source_specification_scales C₀ hC₀,
    hh.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)),eventually_ge_atTop (1:ℝ)] with B hs hlog hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hbase0 : 0 ≤ specificationBase (sourceSystem B) (pathLength B) ⌈C₀*Real.log B⌉₊ := by
    unfold specificationBase; positivity
  apply (specification_polynomial_bound (sourceSystem B) (pathLength B) ⌈C₀*Real.log B⌉₊).trans
  apply (pow_le_pow_left₀ hbase0 hs.2 _).trans
  rw [←Real.rpow_natCast,Real.rpow_def_of_pos (sq_pos_of_pos hB0),Real.log_pow]
  apply Real.exp_le_exp.mpr
  have hl := (div_le_iff₀ (Real.rpow_pos_of_pos hB0 (rho/12))).mp hlog
  have hm := mul_le_mul hs.1 hl (Real.log_nonneg hB) (Real.rpow_nonneg hB0.le _)
  have he : B^(1-rho/3)*((1/2)*B^(rho/12))=(1/2)*B^(1-rho/4) := by
    rw [mul_left_comm,←Real.rpow_add hB0]
    congr 2
    ring
  rw [he] at hm
  norm_num only [Nat.cast_ofNat] at *
  nlinarith

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
