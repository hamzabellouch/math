import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreePrimeSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.OffsetAbsLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Epsilon

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter

def sourceSystem (B : ℝ) : PrimeSystem where
  primes := SourcePrimeBands.corePrimes B ∪ SourcePrimeBands.centerPrimes B
  prime_mem := by
    intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact (mem_filter.mp hp).2.1
  core := SourcePrimeBands.corePrimes B
  core_subset := subset_union_left

def rho : ℝ := 1 / 20
def sourceLength (B : ℝ) : ℕ := 2 * ⌊B⌋₊
def pathLength (B : ℝ) : ℕ := ⌊B ^ (1-rho)⌋₊
def listCutoff (B : ℝ) : ℕ := ⌈B ^ (4*epsilon)⌉₊
def sourceMinPrime (B : ℝ) : ℝ := Real.exp (B ^ (1-epsilon))

lemma source_prime_lower (B : ℝ) (hB : 1 ≤ B) (p : (sourceSystem B).Index) :
    sourceMinPrime B < (p : ℝ) := by
  have he : B ^ (1 - SourcePrimeBands.epsilon) ≤ B ^ (1 - SourcePrimeBands.eta) :=
    Real.rpow_le_rpow_of_exponent_le hB (by norm_num [SourcePrimeBands.epsilon,SourcePrimeBands.eta])
  have hp : p.val.Prime := (sourceSystem B).prime_mem p p.property
  have hlog : B ^ (1-epsilon) < Real.log (p : ℝ) := by
    rcases mem_union.mp p.property with hmem | hmem
    · exact he.trans_lt (mem_filter.mp hmem).2.2
    · exact (mem_filter.mp hmem).2.2
  exact (Real.exp_lt_exp.mpr hlog).trans_eq (Real.exp_log (by exact_mod_cast hp.pos))

lemma sourceLength_le (B : ℝ) (hB : 0 ≤ B) : (sourceLength B : ℝ) ≤ 2 * B := by
  simpa only [sourceLength, Nat.cast_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_left (Nat.floor_le hB) (by norm_num : (0 : ℝ) ≤ 2)

lemma pathLength_le (B : ℝ) (hB : 1 ≤ B) : (pathLength B : ℝ) ≤ B := by
  exact (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
    (Real.rpow_le_self_of_one_le hB (by norm_num [rho]))

lemma listCutoff_le (B : ℝ) (hB : 1 ≤ B) : (listCutoff B : ℝ) ≤ 2 * B := by
  have hp : B ^ (4*epsilon) ≤ B :=
    Real.rpow_le_self_of_one_le hB (by norm_num [epsilon])
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : 0 ≤ B) (4*epsilon))
  change (⌈B^(4*epsilon)⌉₊ : ℝ) ≤ _
  linarith

lemma divisorSlots_le (B C₀ : ℝ) (hB : 1 ≤ B) (hC₀ : 0 ≤ C₀) :
    (⌈C₀ * Real.log B⌉₊ : ℝ) ≤ (C₀+1) * B := by
  have hl := Real.log_le_sub_one_of_pos (by linarith : 0 < B)
  have hc := Nat.ceil_lt_add_one (mul_nonneg hC₀ (Real.log_nonneg hB))
  nlinarith

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma source_lineListSlots_le (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (hB : 1 ≤ B) (hC₀ : 0 ≤ C₀) (hℓ : (ℓ : ℝ) ≤ 2*B)
    (hL : (L : ℝ) ≤ B) (ht : (𝔏.length : ℝ) ≤ 2*B) :
    (lineListSlots w 𝔏 : ℝ) ≤ (4*C₀+6) * B^3 := by
  have hB₀ : 0 ≤ B := by linarith
  have hJ := divisorSlots_le B C₀ hB hC₀
  have hCJ : 0 ≤ (C₀+1)*B := mul_nonneg (by linarith) hB₀
  have hfirst := mul_le_mul hℓ hJ (Nat.cast_nonneg _) (by positivity : 0 ≤ 2*B)
  have hLj := mul_le_mul hL hJ (Nat.cast_nonneg _) hB₀
  have hLj' : (L : ℝ) * (⌈C₀ * Real.log B⌉₊ : ℝ) + 1 ≤ B * ((C₀+1)*B) + 1 := by
    linarith only [hLj]
  have hsecond := mul_le_mul ht hLj'
    (by positivity : 0 ≤ (L : ℝ) * (⌈C₀ * Real.log B⌉₊ : ℝ) + 1)
    (by positivity : 0 ≤ 2*B)
  have hsum := add_le_add hfirst hsecond
  simp only [lineListSlots, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  apply hsum.trans
  have hB2 : B^2 ≤ B^3 := by nlinarith [sq_nonneg (B-1)]
  have hB1 : B ≤ B^3 := by nlinarith [sq_nonneg (B-1)]
  nlinarith

def sourceErrorConstant (h : ℕ) (τ C₀ : ℝ) : ℝ :=
  3 * (4*C₀+6 + 9 * (C₀ + 4*(h : ℝ)*τ) / Real.log 2)

def sourceErrorBound (h : ℕ) (τ C₀ B : ℝ) : ℝ :=
  sourceErrorConstant h τ C₀ * B^4 / sourceMinPrime B

theorem restorationError_source_bound (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (hlabels : ∀ i, w.label i ∈ D.members)
    (hB : 1 ≤ B) (hC₀ : 0 ≤ C₀) (hτ : 0 ≤ τ)
    (hℓ : (ℓ : ℝ) ≤ 2*B) (hL : (L : ℝ) ≤ B) (ht : (𝔏.length : ℝ) ≤ 2*B)
    (hp : ∀ p : S.Index, sourceMinPrime B ≤ (p : ℝ)) :
    restorationError w 𝔏 ≤ sourceErrorBound h τ C₀ B := by
  have hB₀ : 0 ≤ B := by linarith
  have hM₀ : 0 ≤ C₀ + 4*(h : ℝ)*τ := by positivity
  have hh := restorationError_le w 𝔏 hlabels ((C₀+4*(h : ℝ)*τ)*B) (sourceMinPrime B)
    (mul_nonneg hM₀ hB₀) (Real.exp_pos _) hp
    (fun v hv u hu _ => source_line_difference_bound w hlabels hτ hℓ v hv u hu)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  have hs := source_lineListSlots_le w 𝔏 hB hC₀ hℓ hL ht
  have hl : (ℓ : ℝ)+1 ≤ 3*B := by linarith
  have hl2 : ((ℓ : ℝ)+1)^2 ≤ (3*B)^2 := by nlinarith
  have hx := mul_le_mul_of_nonneg_right hl2
    (div_nonneg (mul_nonneg hM₀ hB₀) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  have hsum := add_le_add hs hx
  have hmul := mul_le_mul hl hsum
    (add_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg hM₀ hB₀) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))))
    (by positivity : 0 ≤ 3*B)
  convert hmul using 1
  simp only [sourceErrorConstant]
  ring

theorem sourceErrorBound_tendsto (h : ℕ) (τ C₀ : ℝ) :
    Tendsto (sourceErrorBound h τ C₀) atTop (nhds 0) := by
  have hr : 0 < (1-epsilon) := by norm_num [epsilon]
  have hrne : (1-epsilon) ≠ 0 := hr.ne'
  have hlim := ((isLittleO_rpow_exp_atTop (4/(1-epsilon))).tendsto_div_nhds_zero).comp
    (tendsto_rpow_atTop hr)
  have heq : (fun B : ℝ => (B^(1-epsilon))^(4/(1-epsilon)) / Real.exp (B^(1-epsilon))) =ᶠ[atTop]
      (fun B : ℝ => B^4 / sourceMinPrime B) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    rw [← Real.rpow_mul hB]
    have he : (1-epsilon)*(4/(1-epsilon)) = (4 : ℝ) := by field_simp
    rw [he]
    norm_num [Real.rpow_natCast, sourceMinPrime]
  have hbase : Tendsto (fun B : ℝ => B^4 / sourceMinPrime B) atTop (nhds 0) :=
    hlim.congr' heq
  change Tendsto (fun B : ℝ => sourceErrorConstant h τ C₀ * B^4 / sourceMinPrime B) atTop (nhds 0)
  simpa only [mul_div_assoc, mul_zero] using
    hbase.const_mul (sourceErrorConstant h τ C₀)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
