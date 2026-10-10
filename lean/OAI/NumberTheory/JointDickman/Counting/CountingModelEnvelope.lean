import OAI.NumberTheory.JointDickman.Counting.CountingSiteMoments
import OAI.NumberTheory.JointDickman.Counting.BlockSiteErrorScale

namespace OAI

/-! # A uniform lag envelope at the actual amplification scale -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem countingSiteModel_uniform_envelope
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ R σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀)
    (hroot : independentRootMean B L τ C ≤ R) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      lagEnvelope T (R*C₀/η) i k := by
  apply (countingSiteModel_lag_envelope hMP P m B L T H M τ C c D
    hT hη hC₀ hH hbound i k a b).trans
  unfold lagEnvelope
  split_ifs
  · have hden : 0 ≤ η*(T : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg _)
    have hs : 0 ≤ singularFactor 24 (Nat.dist i.val k.val) :=
      zero_le_one.trans (singularFactor_one_le (by norm_num) _)
    calc
      _ ≤ (R*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hC₀) hden) hs
      _ = _ := by ring
  · exact le_rfl

theorem amplification_sampling_scale : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
    (amplificationMultiplier B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) ∧
    amplificationMultiplier B ≤ auxiliaryCutoff B ∧
    (amplificationMultiplier B : ℝ) ≤ (B : ℝ)^2 ∧
    Real.log (amplificationMultiplier B) ≤ (B : ℝ)/10 ∧
    (B : ℝ)^(32/100 : ℝ)/2 ≤ amplificationMultiplier B := by
  filter_upwards [amplificationMultiplier_valid,amplificationMultiplier_comparable,
    amplification_block_size_le_square 1,eventually_ge_atTop 1] with B hv hc hs hB
  have hs' : amplificationMultiplier B ≤ B^2 := by simpa using hs
  have hcut : B^2 ≤ auxiliaryCutoff B :=
    pow_le_pow_right₀ hB (by norm_num : 2 ≤ 1000)
  refine ⟨hv.1,hv.2,hs'.trans hcut,by exact_mod_cast hs',?_,?_⟩
  · have hlog := Real.log_le_log (by exact_mod_cast hv.1) hv.2
    rw [Real.log_exp] at hlog
    convert hlog using 1
    ring
  · convert hc.2.1 using 1
    norm_num

end JointDickman

end OAI
