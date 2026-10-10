import OAI.Analysis.MarkovType.FiniteProbability
import OAI.Analysis.MarkovType.FiniteSmoothMoments
import Mathlib.Algebra.Module.Submodule.LinearMap

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity.FiniteLaw

variable {Ω K J : Type*} [Fintype Ω] [DecidableEq K] [DecidableEq J]

def fiberWeight (μ : FiniteLaw Ω) (key : Ω → K) (a : K) (ω : Ω) : ℝ :=
  if key ω = a then μ.mass ω else 0

def fiberMass (μ : FiniteLaw Ω) (key : Ω → K) (a : K) : ℝ :=
  ∑ ω, μ.fiberWeight key a ω

def normalizedFiberWeight (μ : FiniteLaw Ω) (key : Ω → K) (a : K) (ω : Ω) : ℝ :=
  (μ.fiberMass key a)⁻¹ * μ.fiberWeight key a ω

theorem fiberWeight_nonneg (μ : FiniteLaw Ω) (key : Ω → K) (a : K) (ω : Ω) :
    0 ≤ μ.fiberWeight key a ω := by
  by_cases h : key ω = a
  · simpa [fiberWeight, h] using μ.mass_nonneg ω
  · simp [fiberWeight, h]

theorem fiberMass_nonneg (μ : FiniteLaw Ω) (key : Ω → K) (a : K) :
    0 ≤ μ.fiberMass key a :=
  Finset.sum_nonneg fun ω _ => μ.fiberWeight_nonneg key a ω

theorem mass_le_fiberMass (μ : FiniteLaw Ω) (key : Ω → K) (ω : Ω) :
    μ.mass ω ≤ μ.fiberMass key (key ω) := by
  have h := Finset.single_le_sum
    (fun ν (_ : ν ∈ (Finset.univ : Finset Ω)) => μ.fiberWeight_nonneg key (key ω) ν)
    (Finset.mem_univ ω)
  have hself : μ.fiberWeight key (key ω) ω = μ.mass ω := ite_eq_left rfl
  rw [hself] at h
  exact h

theorem fiberMass_pos_of_mass_pos (μ : FiniteLaw Ω) (key : Ω → K) {ω : Ω}
    (hω : 0 < μ.mass ω) : 0 < μ.fiberMass key (key ω) :=
  hω.trans_le (μ.mass_le_fiberMass key ω)

theorem fiberWeight_eq_zero_of_fiberMass_eq_zero (μ : FiniteLaw Ω)
    (key : Ω → K) (a : K) (hzero : μ.fiberMass key a = 0) (ω : Ω) :
    μ.fiberWeight key a ω = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg
    (fun ν (_ : ν ∈ (Finset.univ : Finset Ω)) => μ.fiberWeight_nonneg key a ν)).mp
    hzero ω (Finset.mem_univ ω)

theorem normalizedFiberWeight_nonneg (μ : FiniteLaw Ω) (key : Ω → K)
    (a : K) (ω : Ω) : 0 ≤ μ.normalizedFiberWeight key a ω :=
  mul_nonneg (inv_nonneg.mpr (μ.fiberMass_nonneg key a))
    (μ.fiberWeight_nonneg key a ω)

theorem sum_normalizedFiberWeight (μ : FiniteLaw Ω) (key : Ω → K) (a : K)
    (hpos : 0 < μ.fiberMass key a) :
    ∑ ω, μ.normalizedFiberWeight key a ω = 1 := by
  simp only [normalizedFiberWeight, ← Finset.mul_sum]
  change (μ.fiberMass key a)⁻¹ * μ.fiberMass key a = 1
  exact inv_mul_cancel₀ hpos.ne'

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

def fiberSum (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) (a : K) : E :=
  ∑ ω, μ.fiberWeight key a ω • F ω

def conditionalMean (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) (a : K) : E :=
  (μ.fiberMass key a)⁻¹ • μ.fiberSum key F a

def conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) (ω : Ω) : E :=
  μ.conditionalMean key F (key ω)

theorem fiberSum_eq_zero_of_fiberMass_eq_zero (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) (a : K) (hzero : μ.fiberMass key a = 0) :
    μ.fiberSum key F a = 0 := by
  apply Finset.sum_eq_zero
  intro ω _
  rw [μ.fiberWeight_eq_zero_of_fiberMass_eq_zero key a hzero ω, zero_smul]

theorem conditionalMean_eq_zero_of_fiberMass_eq_zero (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) (a : K) (hzero : μ.fiberMass key a = 0) :
    μ.conditionalMean key F a = 0 := by
  simp [conditionalMean, hzero]

theorem conditionalMean_eq_sum_normalizedFiberWeight (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) (a : K) :
    μ.conditionalMean key F a = ∑ ω, μ.normalizedFiberWeight key a ω • F ω := by
  simp only [conditionalMean, fiberSum, normalizedFiberWeight, Finset.smul_sum, smul_smul]

theorem mass_smul_conditionalMean (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (a : K) :
    μ.fiberMass key a • μ.conditionalMean key F a = μ.fiberSum key F a := by
  by_cases hzero : μ.fiberMass key a = 0
  · rw [hzero, zero_smul, μ.fiberSum_eq_zero_of_fiberMass_eq_zero key F a hzero]
  · simp only [conditionalMean, smul_smul, mul_inv_cancel₀ hzero, one_smul]

theorem conditionalAverage_eq_of_key_eq (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) {ω ν : Ω} (h : key ω = key ν) :
    μ.conditionalAverage key F ω = μ.conditionalAverage key F ν := by
  simp only [conditionalAverage, h]

theorem fiberSum_key (μ : FiniteLaw Ω) (key : Ω → K) (G : K → E) (a : K) :
    μ.fiberSum key (fun ω => G (key ω)) a = μ.fiberMass key a • G a := by
  simp only [fiberSum, fiberMass, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : key ω = a <;> simp [fiberWeight, h]

theorem conditionalMean_key (μ : FiniteLaw Ω) (key : Ω → K) (G : K → E)
    (a : K) (hpos : 0 < μ.fiberMass key a) :
    μ.conditionalMean key (fun ω => G (key ω)) a = G a := by
  rw [conditionalMean, μ.fiberSum_key, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

theorem conditionalAverage_key_of_mass_pos (μ : FiniteLaw Ω) (key : Ω → K)
    (G : K → E) (ω : Ω) (hpos : 0 < μ.mass ω) :
    μ.conditionalAverage key (fun ν => G (key ν)) ω = G (key ω) :=
  μ.conditionalMean_key key G (key ω) (μ.fiberMass_pos_of_mass_pos key hpos)

theorem mass_smul_conditionalAverage_key (μ : FiniteLaw Ω) (key : Ω → K)
    (G : K → E) (ω : Ω) :
    μ.mass ω • μ.conditionalAverage key (fun ν => G (key ν)) ω =
      μ.mass ω • G (key ω) := by
  by_cases hzero : μ.mass ω = 0
  · simp only [hzero, zero_smul]
  · have hpos : 0 < μ.mass ω := lt_of_le_of_ne (μ.mass_nonneg ω) (Ne.symm hzero)
    rw [μ.conditionalAverage_key_of_mass_pos key G ω hpos]

theorem fiberSum_eq_vexpect_indicator (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (a : K) :
    μ.fiberSum key F a = μ.vexpect (fun ω => if key ω = a then F ω else 0) := by
  simp only [fiberSum, vexpect]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : key ω = a <;> simp [fiberWeight, h]

variable [Fintype K]

theorem sum_fiberSum (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) :
    ∑ a, μ.fiberSum key F a = μ.vexpect F := by
  simp only [fiberSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_smul]

theorem vexpect_key (μ : FiniteLaw Ω) (key : Ω → K) (G : K → E) :
    μ.vexpect (fun ω => G (key ω)) = ∑ a, μ.fiberMass key a • G a := by
  symm
  simp only [fiberMass, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_smul]

theorem vexpect_key_smul (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (c : K → ℝ) :
    μ.vexpect (fun ω => c (key ω) • F ω) = ∑ a, c a • μ.fiberSum key F a := by
  symm
  simp only [fiberSum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, smul_smul, mul_comm, ite_smul]

theorem vexpect_key_smul_eq_zero (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (hzero : ∀ a, μ.fiberSum key F a = 0) (c : K → ℝ) :
    μ.vexpect (fun ω => c (key ω) • F ω) = 0 := by
  rw [μ.vexpect_key_smul key F c]
  simp only [hzero, smul_zero, Finset.sum_const_zero]

theorem vexpect_key_indicator_eq_zero (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (hzero : ∀ a, μ.fiberSum key F a = 0)
    (P : K → Prop) [DecidablePred P] :
    μ.vexpect (fun ω => if P (key ω) then F ω else 0) = 0 := by
  simpa only [ite_smul, one_smul, zero_smul] using
    μ.vexpect_key_smul_eq_zero key F hzero (fun a => if P a then 1 else 0)

theorem vexpect_conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K) (F : Ω → E) :
    μ.vexpect (μ.conditionalAverage key F) = μ.vexpect F := by
  change μ.vexpect (fun ω => μ.conditionalMean key F (key ω)) = _
  rw [μ.vexpect_key]
  simp only [μ.mass_smul_conditionalMean]
  exact μ.sum_fiberSum key F

theorem vexpect_key_smul_conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (c : K → ℝ) :
    μ.vexpect (fun ω => c (key ω) • μ.conditionalAverage key F ω) =
      μ.vexpect (fun ω => c (key ω) • F ω) := by
  change μ.vexpect (fun ω => (fun a => c a • μ.conditionalMean key F a) (key ω)) = _
  rw [μ.vexpect_key key (fun a => c a • μ.conditionalMean key F a),
    μ.vexpect_key_smul key F c]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_smul, mul_comm (μ.fiberMass key a) (c a), ← smul_smul,
    μ.mass_smul_conditionalMean]

theorem fiberSum_conditionalAverage_comp (μ : FiniteLaw Ω) (key : Ω → K)
    (parent : K → J) (F : Ω → E) (a : J) :
    μ.fiberSum (parent ∘ key) (μ.conditionalAverage key F) a =
      μ.fiberSum (parent ∘ key) F a := by
  rw [μ.fiberSum_eq_vexpect_indicator, μ.fiberSum_eq_vexpect_indicator]
  simpa only [Function.comp_apply, ite_smul, one_smul, zero_smul] using
    μ.vexpect_key_smul_conditionalAverage key F
      (fun b => if parent b = a then 1 else 0)

theorem conditionalAverage_tower (μ : FiniteLaw Ω) (key : Ω → K)
    (parent : K → J) (F : Ω → E) (ω : Ω) :
    μ.conditionalAverage (parent ∘ key) (μ.conditionalAverage key F) ω =
      μ.conditionalAverage (parent ∘ key) F ω := by
  exact congrArg (fun z : E => (μ.fiberMass (parent ∘ key) ((parent ∘ key) ω))⁻¹ • z)
    (μ.fiberSum_conditionalAverage_comp key parent F ((parent ∘ key) ω))

end Module

section Pairing

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype K]

theorem expect_pair_key_right (μ : FiniteLaw Ω) (key : Ω → K)
    (G : Ω → E →ₗ[ℝ] ℝ) (H : K → E) :
    μ.expect (fun ω => G ω (H (key ω))) = ∑ a, (μ.fiberSum key G a) (H a) := by
  symm
  simp only [fiberSum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_mul]

theorem expect_pair_key_left (μ : FiniteLaw Ω) (key : Ω → K)
    (H : K → E →ₗ[ℝ] ℝ) (F : Ω → E) :
    μ.expect (fun ω => H (key ω) (F ω)) = ∑ a, H a (μ.fiberSum key F a) := by
  symm
  simp only [fiberSum, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [fiberWeight, ite_mul]

theorem expect_pair_conditionalAverage (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) (G : Ω → E →ₗ[ℝ] ℝ) :
    μ.expect (fun ω => G ω (μ.conditionalAverage key F ω)) =
      μ.expect (fun ω => (μ.conditionalAverage key G ω) (F ω)) := by
  change μ.expect (fun ω => G ω (μ.conditionalMean key F (key ω))) =
    μ.expect (fun ω => (μ.conditionalMean key G (key ω)) (F ω))
  rw [μ.expect_pair_key_right, μ.expect_pair_key_left]
  apply Finset.sum_congr rfl
  intro a _
  simp only [conditionalMean, map_smul, LinearMap.smul_apply]

end Pairing

theorem expect_conditionalAverage [Fintype K] (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → ℝ) :
    μ.expect (μ.conditionalAverage key F) = μ.expect F := by
  simpa only [expect, vexpect, smul_eq_mul] using μ.vexpect_conditionalAverage key F

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conditionalMean_norm_rpow_le (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) {q : ℝ} (hq : 1 ≤ q) (a : K) :
    ‖μ.conditionalMean key F a‖ ^ q ≤
      μ.conditionalMean key (fun ω => ‖F ω‖ ^ q) a := by
  by_cases hzero : μ.fiberMass key a = 0
  · have hqne : q ≠ 0 := by linarith
    simp [conditionalMean, hzero, Real.zero_rpow hqne]
  · have hpos : 0 < μ.fiberMass key a :=
      lt_of_le_of_ne (μ.fiberMass_nonneg key a) (Ne.symm hzero)
    have hj := finite_norm_rpow_jensen (μ.normalizedFiberWeight key a) F
      (μ.normalizedFiberWeight_nonneg key a) (μ.sum_normalizedFiberWeight key a hpos) hq
    rw [← μ.conditionalMean_eq_sum_normalizedFiberWeight key F a] at hj
    simpa only [conditionalMean, fiberSum, normalizedFiberWeight, smul_eq_mul,
      Finset.mul_sum, mul_assoc] using hj

theorem conditionalAverage_norm_rpow_le (μ : FiniteLaw Ω) (key : Ω → K)
    (F : Ω → E) {q : ℝ} (hq : 1 ≤ q) (ω : Ω) :
    ‖μ.conditionalAverage key F ω‖ ^ q ≤
      μ.conditionalAverage key (fun ν => ‖F ν‖ ^ q) ω :=
  μ.conditionalMean_norm_rpow_le key F hq (key ω)

theorem expect_norm_conditionalAverage_rpow_le [Fintype K] (μ : FiniteLaw Ω)
    (key : Ω → K) (F : Ω → E) {q : ℝ} (hq : 1 ≤ q) :
    μ.expect (fun ω => ‖μ.conditionalAverage key F ω‖ ^ q) ≤
      μ.expect (fun ω => ‖F ω‖ ^ q) := by
  calc
    _ ≤ μ.expect (μ.conditionalAverage key (fun ω => ‖F ω‖ ^ q)) :=
      μ.expect_mono (μ.conditionalAverage_norm_rpow_le key F hq)
    _ = _ := μ.expect_conditionalAverage key (fun ω => ‖F ω‖ ^ q)

end MarkovSuperreflexivity.FiniteLaw

end

end OAI
