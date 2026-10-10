import OAI.Analysis.MarkovType.DyadicIndependentBlocks
import OAI.Analysis.MarkovType.DyadicWeakMaxDefinition
import OAI.Analysis.MarkovType.FiniteTailAmplification

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem prob_nonneg (μ : FiniteLaw Ω) (A : Ω → Prop) : 0 ≤ μ.prob A := by
  classical
  exact Finset.sum_nonneg fun ω _ => by
    split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl

theorem prob_mono (μ : FiniteLaw Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    μ.prob A ≤ μ.prob B := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω
  · simp only [ite_eq_left ha, ite_eq_left (h ω ha)]
    exact le_rfl
  · simp only [ite_eq_right ha]
    split_ifs <;> first | exact μ.mass_nonneg ω | exact le_rfl

theorem prob_le_one (μ : FiniteLaw Ω) (A : Ω → Prop) : μ.prob A ≤ 1 := by
  simpa only [prob_true] using μ.prob_mono (B := fun _ => True) (fun _ _ => trivial)

end FiniteLaw

def dyadicAmplificationThreshold (a A : ℝ) : ℝ := (2 * A) ^ (2 / a)
def dyadicAmplificationRadius (a A : ℝ) : ℝ := 2 * dyadicAmplificationThreshold a A
def dyadicZeroWeakConstant (a A : ℝ) : ℝ := 2 * (dyadicAmplificationRadius a A) ^ a

theorem dyadicAmplificationThreshold_pos {a A : ℝ} (hA : 1 ≤ A) :
    0 < dyadicAmplificationThreshold a A :=
  Real.rpow_pos_of_pos (by linarith) _

theorem dyadicAmplificationRadius_pos {a A : ℝ} (hA : 1 ≤ A) :
    0 < dyadicAmplificationRadius a A :=
  mul_pos (by norm_num) (dyadicAmplificationThreshold_pos hA)

theorem dyadicAmplificationThreshold_power {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    (dyadicAmplificationThreshold a A) ^ (a / 2) = 2 * A := by
  unfold dyadicAmplificationThreshold
  rw [← Real.rpow_mul (by linarith : 0 ≤ 2 * A)]
  rw [show (2 / a) * (a / 2) = 1 by field_simp [ha.ne'], Real.rpow_one]

theorem dyadicZeroWeakConstant_ge_one {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A) :
    1 ≤ dyadicZeroWeakConstant a A := by
  have hu : 1 ≤ dyadicAmplificationThreshold a A :=
    Real.one_le_rpow (by linarith) (div_nonneg (by norm_num) ha.le)
  have hR : 1 ≤ dyadicAmplificationRadius a A := by
    unfold dyadicAmplificationRadius
    linarith
  have hRp := Real.one_le_rpow hR ha.le
  unfold dyadicZeroWeakConstant
  linarith

theorem dyadic_half_power_scale {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (hinput : finiteMoment dyadicInputWeight a φ ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    (1 / 2 : ℝ) ≤ (1 - (dyadicLaw N).prob (fun ω =>
      dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a) < ‖dyadicSynthesis N φ ω‖)) ^ m := by
  classical
  let u := dyadicAmplificationThreshold a A
  let G := dyadicIndependentBlocks m (dyadicCopyScale m a) φ
  let bad : DyadicWord (m * N) → Prop :=
    fun ω => ∃ j : ℕ, j ≤ m * N ∧ u < ‖dyadicProcess G j ω‖
  have hu : 0 < u := dyadicAmplificationThreshold_pos hA
  have hGinput : finiteMoment dyadicInputWeight a G ≤ 1 := by
    dsimp only [G]
    rw [dyadicIndependentBlocks_normalized hm φ hroot ha]
    exact hinput
  have hbad : (dyadicLaw (m * N)).prob bad ≤ 1 / 2 := by
    have hh := hmax (m * N) G (dyadicIndependentBlocks_root _ _ _) hGinput u hu
    have hpow : u ^ (a / 2) = 2 * A := dyadicAmplificationThreshold_power ha hA
    have hApos : 0 < A := by linarith
    have hratio : A / (2 * A) = (1 / 2 : ℝ) := by field_simp [hApos.ne']
    simpa only [hpow, hratio] using hh
  have hgood : (1 / 2 : ℝ) ≤ (dyadicLaw (m * N)).prob (fun ω => ¬ bad ω) := by
    rw [FiniteLaw.prob_not]
    linarith
  have hsub : (dyadicLaw (m * N)).prob (fun ω => ¬ bad ω) ≤
      (dyadicLaw (m * N)).prob (fun ω => ∀ b : Fin m,
        ‖dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ ≤
          dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a)) := by
    apply FiniteLaw.prob_mono
    intro ω hω b
    have hb : ∀ j : ℕ, j ≤ m * N → ‖dyadicProcess G j ω‖ ≤ u := by
      intro j hj
      exact le_of_not_gt (fun hh => hω ⟨j, hj, hh⟩)
    have hcopy := dyadicIndependentBlocks_copy_norm_le
      (dyadicCopyScale m a) φ hroot ω hb b
    have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hpowpos : 0 < (m : ℝ) ^ (1 / a) := Real.rpow_pos_of_pos hmpos _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (dyadicCopyScale_pos hm a)] at hcopy
    have hdiv : ‖dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ /
        (m : ℝ) ^ (1 / a) ≤ 2 * u := by
      simpa only [dyadicCopyScale, div_eq_mul_inv, mul_comm] using hcopy
    exact (div_le_iff₀ hpowpos).mp hdiv
  have heq : (dyadicLaw (m * N)).prob (fun ω => ∀ b : Fin m,
        ‖dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ ≤
          dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a)) =
      (1 - (dyadicLaw N).prob (fun ω =>
        dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a) < ‖dyadicSynthesis N φ ω‖)) ^ m := by
    rw [dyadicBlock_prob m N (fun x => ∀ b : Fin m,
      ‖dyadicSynthesis N φ (x b)‖ ≤ dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a))]
    exact FiniteLaw.independentCopies_prob_all_norm_le (dyadicLaw N) m
      (dyadicSynthesis N φ) (dyadicAmplificationRadius a A * (m : ℝ) ^ (1 / a))
  exact heq ▸ hgood.trans hsub

theorem dyadic_normalized_zero_tail {a A : ℝ} (ha : 0 < a) (hA : 1 ≤ A)
    (hmax : DyadicNormalizedWeakMax E a A) {N : ℕ} (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (hinput : finiteMoment dyadicInputWeight a φ ≤ 1)
    (t : ℝ) (ht : 0 < t) :
    (dyadicLaw N).prob (fun ω => t < ‖dyadicSynthesis N φ ω‖) ≤
      dyadicZeroWeakConstant a A / t ^ a := by
  apply tail_bound_of_half_power_scale
    (fun s => (dyadicLaw N).prob (fun ω => s < ‖dyadicSynthesis N φ ω‖))
    ha (dyadicAmplificationRadius_pos hA)
    (fun s hs v hv hsv => (dyadicLaw N).prob_mono (fun ω h => hsv.trans_lt h))
    (fun _ _ => FiniteLaw.prob_nonneg _ _) (fun _ _ => FiniteLaw.prob_le_one _ _)
    (fun m hm => dyadic_half_power_scale ha hA hmax φ hroot hinput m hm) t ht

end MarkovSuperreflexivity

end

end OAI
