import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallGram
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealGramDeterminantOrder

namespace OAI

/-! # Increasing positive word-ball Gram matrices -/
noncomputable section
namespace PolycyclicRecognition
open Finset Matrix
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem wordBallGram_eq_sum (S : Finset G) (R : ℕ) (F : ι → G → ℝ) :
    wordBallGram S R F = ∑ x ∈ wordBall S R, vecMulVec (fun i => F i x) (fun i => F i x) := by
  ext i j
  simp only [wordBallGram_apply, Matrix.sum_apply, vecMulVec_apply]

omit [DecidableEq ι] in
theorem wordBallGram_posSemidef (S : Finset G) (R : ℕ) (F : ι → G → ℝ) :
    (wordBallGram S R F).PosSemidef := by
  rw [wordBallGram_eq_sum]
  apply Matrix.posSemidef_sum
  intro x _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => F i x)

omit [DecidableEq ι] in
theorem wordBallGram_sub_posSemidef (S : Finset G) (F : ι → G → ℝ)
    {m n : ℕ} (hmn : m ≤ n) :
    (wordBallGram S n F - wordBallGram S m F).PosSemidef := by
  have he : wordBallGram S n F - wordBallGram S m F =
      ∑ x ∈ wordBall S n \ wordBall S m, vecMulVec (fun i => F i x) (fun i => F i x) := by
    rw [wordBallGram_eq_sum, wordBallGram_eq_sum]
    exact (eq_sub_iff_add_eq.mpr (sum_sdiff (wordBall_mono S hmn))).symm
  rw [he]
  apply Matrix.posSemidef_sum
  intro x _
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun i => F i x)

omit [DecidableEq ι] in
theorem wordBallGram_posDef_mono (S : Finset G) (F : ι → G → ℝ)
    {m n : ℕ} (hmn : m ≤ n) (hm : (wordBallGram S m F).PosDef) :
    (wordBallGram S n F).PosDef := by
  have h := hm.add_posSemidef (wordBallGram_sub_posSemidef S F hmn)
  simpa using h

theorem wordBallGram_det_mono (S : Finset G) (F : ι → G → ℝ)
    {m n : ℕ} (hmn : m ≤ n) (hm : (wordBallGram S m F).PosDef) :
    (wordBallGram S m F).det ≤ (wordBallGram S n F).det :=
  real_posDef_det_mono hm (wordBallGram_sub_posSemidef S F hmn)

theorem wordBallGram_det_monotone (S : Finset G) (F : ι → G → ℝ) :
    Monotone (fun R => (wordBallGram S R F).det) := by
  intro m n hmn
  exact real_posSemidef_det_mono (wordBallGram_posSemidef S m F)
    (wordBallGram_sub_posSemidef S F hmn)

end PolycyclicRecognition

end

end OAI
