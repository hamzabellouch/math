import Mathlib
import OAI.Computability.VertexCover.Fourier.Walsh

namespace OAI

                                                                                        

noncomputable section

namespace UniqueGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def support (s : Cube I) : Finset I := Finset.univ.filter fun i => s i = true

def noiseWeight (ε : ℝ) (μ : Cube I) : ℝ :=
  ∏ i, if μ i then ε else 1 - ε

omit [DecidableEq I] in
theorem noiseWeight_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) (μ : Cube I) :
    0 ≤ noiseWeight ε μ := by
  apply Finset.prod_nonneg
  intro i _
  split <;> linarith

theorem noiseWeight_sum (ε : ℝ) : (∑ μ : Cube I, noiseWeight ε μ) = 1 := by
  unfold noiseWeight
  rw [← Fintype.prod_sum (fun (_ : I) (b : Bool) => if b then ε else 1 - ε)]
  simp []

theorem noise_walsh (ε : ℝ) (s : Cube I) :
    (∑ μ, noiseWeight ε μ * walsh s μ) = (1 - 2 * ε) ^ (support s).card := by
  unfold noiseWeight walsh
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    (if b then ε else 1 - ε) * bitSign (s i && b))]
  have hc (i : I) : (∑ b : Bool,
      (if b then ε else 1 - ε) * bitSign (s i && b)) =
        if s i then 1 - 2 * ε else 1 := by
    cases s i <;> simp [bitSign] ; ring
  simp_rw [hc]
  simp [support, Finset.prod_ite]

def thirdQuery (π : J → I) (f : Cube I) (g μ : Cube J) : Cube J :=
  cubeXor g (cubeXor (fun y => f (π y)) μ)

theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

def projectedCoefficient (π : J → I) (A : Cube I → ℝ) (s : Cube J) : ℝ :=
  𝔼 f, A f * walsh s (fun y => f (π y))

def testBias (ε : ℝ) (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ * A f *
    (𝔼 g, B g * B (thirdQuery π f g μ))

theorem testBias_fourier (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → ℝ) :
    testBias ε π A B = ∑ s,
      projectedCoefficient π A s * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
  unfold testBias thirdQuery
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (f : Cube I) :
      (∑ μ, noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * walsh s (cubeXor (fun y => f (π y)) μ))) =
      (A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
    simp_rw [walsh_xor]
    have heq (μ : Cube J) : noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * (walsh s (fun y => f (π y)) * walsh s μ)) =
      ((A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2) *
        (noiseWeight ε μ * walsh s μ) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, noise_walsh]
  simp_rw [hterm, ← Finset.expect_mul]
  rfl

def testAcceptance (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  𝔼 f, ∑ μ, noiseWeight ε μ *
    (𝔼 g, if A f ^^ B g ^^ B (thirdQuery π f g μ) then 0 else 1)

theorem threeBit_indicator (a b «c» : Bool) :
    (if a ^^ b ^^ «c» then (0 : ℝ) else 1) =
      (1 + bitSign a * bitSign b * bitSign «c») / 2 := by
  cases a <;> cases b <;> cases «c» <;> norm_num [bitSign]

theorem testAcceptance_eq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) :
    testAcceptance ε π A B =
      (1 + testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g))) / 2 := by
  unfold testAcceptance testBias
  simp_rw [threeBit_indicator, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp only [Fintype.expect_const]
  have hterm (f : Cube I) (μ : Cube J) :
      noiseWeight ε μ * ((1 + 𝔼 g,
        bitSign (A f) * bitSign (B g) * bitSign (B (thirdQuery π f g μ))) * 2⁻¹) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (A f) *
        (𝔼 g, bitSign (B g) * bitSign (B (thirdQuery π f g μ)))) * 2⁻¹ := by
    simp_rw [mul_assoc (bitSign (A f)), ← Finset.mul_expect]
    ring
  simp_rw [hterm, ← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum,
    ← Finset.expect_mul, Finset.expect_add_distrib]
  simp

end UniqueGames.Foundations.Hastad
end

end OAI
