import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallGramOrder
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicGoodScales

namespace OAI

/-! # Polynomial growth of the combined volume and Gram determinant

Raising the ball volume to the dimension avoids fractional powers in the
scale-selection quantity from Kleiner, Section 3.1.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset Matrix
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordBallVolumeDeterminant (S : Finset G) (F : ι → G → ℝ) (R : ℕ) : ℝ :=
  ((wordBall S R).card : ℝ) ^ Fintype.card ι * (wordBallGram S R F).det

theorem wordBallVolumeDeterminant_nonneg (S : Finset G) (F : ι → G → ℝ) (R : ℕ) :
    0 ≤ wordBallVolumeDeterminant S F R :=
  mul_nonneg (by positivity) (wordBallGram_posSemidef S R F).det_nonneg

theorem wordBallVolumeDeterminant_monotone (S : Finset G) (F : ι → G → ℝ) :
    Monotone (wordBallVolumeDeterminant S F) := by
  intro m n hmn
  exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (card_le_card (wordBall_mono S hmn))) _)
    (wordBallGram_det_monotone S F hmn) (wordBallGram_posSemidef S m F).det_nonneg
    (by positivity)

theorem wordBallVolumeDeterminant_pos (S : Finset G) (F : ι → G → ℝ) (R : ℕ)
    (hR : (wordBallGram S R F).PosDef) : 0 < wordBallVolumeDeterminant S F R := by
  exact mul_pos (pow_pos (Nat.cast_pos.mpr
    (card_pos.mpr ⟨1, one_mem_wordBall S R⟩)) _) hR.det_pos

theorem wordBallVolumeDeterminant_polynomial_bound (S : Finset G)
    (d b : ℕ) (F : ι → G → ℝ)
    (hF : ∀ i, PolynomiallyBoundedOnWords S d (F i))
    (D : ℝ) (hD : 0 ≤ D)
    (hvol : ∀ R, ((wordBall S R).card : ℝ) ≤ D * (1 + (R : ℝ)) ^ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R, wordBallVolumeDeterminant S F R ≤
      M * (1 + (R : ℝ)) ^ ((2 * b + 2 * d) * Fintype.card ι) := by
  obtain ⟨C, hC, hbound⟩ := finite_family_polynomial_word_bound S d F hF
  refine ⟨(Fintype.card ι).factorial * (D ^ 2 * C ^ 2) ^ Fintype.card ι,
    by positivity, fun R => ?_⟩
  have hd := wordBallGram_det_bound S R d b F C D hC (fun i x hx => hbound i R x hx) (hvol R)
  have hv := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (wordBall S R).card)
    (hvol R) (Fintype.card ι)
  calc
    _ ≤ ((wordBall S R).card : ℝ) ^ Fintype.card ι * |(wordBallGram S R F).det| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ (D * (1 + (R : ℝ)) ^ b) ^ Fintype.card ι *
        ((Fintype.card ι).factorial * (D * C ^ 2) ^ Fintype.card ι *
          (1 + (R : ℝ)) ^ ((b + 2 * d) * Fintype.card ι)) :=
      mul_le_mul hv hd (abs_nonneg _) (by positivity)
    _ = _ := by
      have he : (2 * b + 2 * d) * Fintype.card ι =
          b * Fintype.card ι + (b + 2 * d) * Fintype.card ι := by ring
      have hc : (D ^ 2 * C ^ 2) ^ Fintype.card ι =
          D ^ Fintype.card ι * (D * C ^ 2) ^ Fintype.card ι := by
        rw [← mul_pow]
        ring
      rw [hc, he, pow_add, mul_pow, ← pow_mul]
      ring

theorem polynomial_sequence_exponential_bound (v : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (p : ℕ) (hv : ∀ R, v R ≤ M * (1 + (R : ℝ)) ^ p) (a : ℕ) :
    ∀ n, v (a + 16 ^ n) ≤ (M * ((a : ℝ) + 2) ^ p) * ((16 : ℝ) ^ p) ^ n := by
  intro n
  have hn : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
  have hb : 1 + ((a + 16 ^ n : ℕ) : ℝ) ≤ ((a : ℝ) + 2) * 16 ^ n := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) a) (sub_nonneg.mpr hn)]
  calc
    _ ≤ M * (1 + ((a + 16 ^ n : ℕ) : ℝ)) ^ p := hv _
    _ ≤ M * (((a : ℝ) + 2) * 16 ^ n) ^ p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb p) hM
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm n p, pow_mul]; ring

theorem exists_wordBall_volume_determinant_good_scales (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V) (d b : ℕ)
    (hF : ∀ i, PolynomiallyBoundedOnWords S d (basis i).val)
    (D : ℝ) (hD : 0 ≤ D)
    (hvol : ∀ R, ((wordBall S R).card : ℝ) ≤ D * (1 + (R : ℝ)) ^ b) :
    let F := fun i => (basis i).val
    let p := (2 * b + 2 * d) * Fintype.card ι
    let A := 2 * ((16 : ℝ) ^ p) ^ 3
    ∃ a : ℕ, (wordBallGram S a F).PosDef ∧ ∀ L w : ℕ, 0 < w → ∃ i j : ℕ,
      L ≤ i ∧ w < j - i ∧ j - i < 3 * w ∧
      wordBallVolumeDeterminant S F (a + 16 ^ (i + 1)) ≤
        A * wordBallVolumeDeterminant S F (a + 16 ^ i) ∧
      wordBallVolumeDeterminant S F (a + 16 ^ (j + 1)) ≤
        A * wordBallVolumeDeterminant S F (a + 16 ^ j) ∧
      wordBallVolumeDeterminant S F (a + 16 ^ (j + 1)) ≤
        A ^ w * wordBallVolumeDeterminant S F (a + 16 ^ i) := by
  dsimp only
  let F := fun i => (basis i).val
  let p := (2 * b + 2 * d) * Fintype.card ι
  obtain ⟨a, ha⟩ := exists_wordBallGram_posDef S hS hgen V basis
  obtain ⟨M, hM, hb⟩ := wordBallVolumeDeterminant_polynomial_bound S d b F hF D hD hvol
  let v := fun n => wordBallVolumeDeterminant S F (a + 16 ^ n)
  have hv : Monotone v := by
    intro m n hmn
    apply wordBallVolumeDeterminant_monotone S F
    exact Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) hmn) a
  have hp : ∀ n, 0 < v n := by
    intro n
    exact wordBallVolumeDeterminant_pos S F _ (wordBallGram_posDef_mono S F
      (Nat.le_add_right a (16 ^ n)) ha)
  refine ⟨a, ha, fun L w hw => ?_⟩
  exact exponential_growth_two_good_scales v hv hp (pow_pos (by norm_num) p)
    (polynomial_sequence_exponential_bound (wordBallVolumeDeterminant S F) hM p hb a) L w hw

end PolycyclicRecognition

end

end OAI
