import OAI.NumberTheory.DirichletL.GammaDetectorExpansion
import OAI.NumberTheory.DirichletL.Hecke.DetectorBudget

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorLower
open HeckeFamily HeckeDetectorTail HeckeDetectorFinite HeckeDetectorPartition
open GammaZeroDetector
local notation "O" => HeckeFamily.O

lemma unit_term_lower (U : ℝ) (hU : 2 ≤ U) :
    (3/4 : ℝ) ≤ ‖Complex.exp (-1/((U^20 : ℝ) : ℂ))‖ := by
  have hUp : 0 < U := by linarith
  have hp : 4 ≤ U^20 := by
    calc
      4 ≤ U^2 := by nlinarith
      _ ≤ U^20 := pow_le_pow_right₀ (by linarith : 1 ≤ U) (by norm_num : 2 ≤ 20)
  have hi : 1/(U^20) ≤ (1/4 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hp
  rw [Complex.norm_exp]
  have he : (-1/((U^20 : ℝ) : ℂ)).re = -1/(U^20) := by
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,←Complex.ofReal_div,Complex.ofReal_re]
  rw [he]
  have hh := Real.add_one_le_exp (-1/(U^20))
  simp only [neg_div] at hh ⊢
  linarith

theorem terminal_uniform_lower (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      (1/2 : ℝ) ≤ ‖∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I‖ := by
  obtain ⟨UG,hUG⟩ := detector_uniform_small R θ (1/8) hR hθ hθ' (by norm_num)
  obtain ⟨UT,hUT⟩ := terminalRemainder_uniform_small 1 1 (1/8) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max 2 (max UG UT),?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hU1 : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  have hg := hUG U ((le_max_left UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ hχ V hVb D (by linarith) hDU hQ ρ hρ hzero hheight
  have ht := hUT U ((le_max_right UG UT).trans ((le_max_right 2 _).trans hU)) hU1
    χ V T hVb hTb hTone D ρ (by linarith)
  have hi := terminal_sum_identity χ V T 1 1 D (U^20) (U^21) (by norm_num)
    hVb hTb hD (by positivity) hVone hVzero ρ (by linarith)
  rw [(GammaDetectorExpansion.detector_hasSum_convolution χ V
    (by linarith : 0 < D) (by positivity : 0 < U^20) hVzero (by linarith : -1 < ρ.re)).tsum_eq] at hi
  have he : Complex.exp (-1/((U^20 : ℝ) : ℂ)) =
      detectorIntegral χ V D (U^20) ρ -
        (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I) -
        (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I) := by
    rw [hi]
    ring
  have hn := norm_sub_le
    (detectorIntegral χ V D (U^20) ρ - ∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
    (∑' I : Ideal O, terminalTerm χ V T D (U^20) (U^21) ρ I)
  rw [←he] at hn
  have hn' := norm_sub_le (detectorIntegral χ V D (U^20) ρ)
    (∑' I : Ideal O, terminalRemainder χ V T D (U^20) (U^21) ρ I)
  have hu := unit_term_lower U hU2
  linarith

theorem exists_dyadic_zero_witness (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθ' : θ < 3/4) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → (∀ x : ℝ, ‖T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) →
      ∀ D : ℝ, 2 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ∃ j ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
        ∃ k ∈ Finset.range (length (⌈2*U^21⌉₊ : ℝ)+1),
          (1/2 : ℝ) ≤ 625*(Real.logb 2 U)^2*‖dyadicBlock χ V T D (U^20) (U^21) ρ j k‖ ∧
          (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
          (2 : ℝ)^j*(2 : ℝ)^k < 8*U^21 := by
  obtain ⟨U₁,hU₁⟩ := terminal_uniform_lower R θ hR hθ hθ'
  refine ⟨max 2 U₁,?_⟩
  intro U hU χ hχ V T hVb hTb hVone hVzero hTone hTzero D hD hDU hQ ρ hρ hzero hheight
  have hU2 : 2 ≤ U := (le_max_left _ _).trans hU
  have hUpos : 0 < U := by linarith
  have ht := hU₁ U ((le_max_right _ _).trans hU) χ hχ V T hVb hTb hVone hVzero hTone D hD hDU hQ ρ hρ hzero hheight
  obtain ⟨j,hj,k,hk,hb⟩ := exists_dyadic_block χ V T D (U^20) (U^21)
    (by positivity) hTzero hVone hVzero ρ (1/2) ht
  have hbn : dyadicBlock χ V T D (U^20) (U^21) ρ j k ≠ 0 := by
    intro hz
    rw [hz,norm_zero,mul_zero] at hb
    norm_num at hb
  refine ⟨j,hj,k,hk,?_,nonzero_block_scale_bounds χ V T D (U^20) (U^21)
    (by linarith) (by positivity) hTzero hVone hVzero ρ j k hbn⟩
  exact hb.trans (mul_le_mul_of_nonneg_right
    (HeckeDetectorBudget.source_pair_count_bound U hU2) (norm_nonneg _))

end SevenEighths.HeckeDetectorLower

end

end OAI
