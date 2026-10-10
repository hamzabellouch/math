import OAI.NumberTheory.ShortEgyptian.ParameterBounds

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def charSum {q : ℕ} [NeZero q] (A : Finset (ZMod q)) (k : ZMod q) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar (k * a)

noncomputable def probabilityFourier {q : ℕ} [NeZero q] (μ : ZMod q → ℝ) (k : ZMod q) : ℂ :=
  ∑ x : ZMod q, (μ x : ℂ) * ZMod.stdAddChar (-(k * x))

@[simp] theorem stdAddChar_norm {q : ℕ} [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

@[simp] theorem charSum_zero {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    charSum A 0 = A.card := by simp [charSum]

@[simp] theorem probabilityFourier_zero {q : ℕ} [NeZero q] (μ : ZMod q → ℝ)
    (hμ : ∑ x, μ x = 1) : probabilityFourier μ 0 = 1 := by
  simp only [probabilityFourier, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  exact_mod_cast hμ

theorem probabilityFourier_norm {q : ℕ} [NeZero q] (μ : ZMod q → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1) (k : ZMod q) :
    ‖probabilityFourier μ k‖ ≤ 1 := by
  calc
    _ ≤ ∑ x : ZMod q, ‖(μ x : ℂ) * ZMod.stdAddChar (-(k * x))‖ := norm_sum_le _ _
    _ = 1 := by simp [abs_of_nonneg (hμ _), hmass]

theorem charSum_energy {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    ∑ k : ZMod q, ‖charSum A k‖ ^ 2 = (q : ℝ) * A.card := by
  classical
  have hh := finite_parseval (q := q) (fun x => if x ∈ A then (1 : ℂ) else 0)
  simpa [charSum, ite_mul, apply_ite, ite_pow] using hh

theorem charSum_l1_bound {q : ℕ} [NeZero q] (A B : Finset (ZMod q))
    (hcard : A.card ≤ 4 * B.card) :
    ∑ k : ZMod q, ‖charSum A k‖ * ‖charSum B k‖ ≤ 2 * q * B.card := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun k => ‖charSum A k‖) (fun k => ‖charSum B k‖)
  rw [charSum_energy, charSum_energy] at hc
  have hcard' : (A.card : ℝ) ≤ 4 * B.card := by exact_mod_cast hcard
  have hbd : (q : ℝ) * A.card * (q * B.card) ≤ (2 * q * B.card) ^ 2 := by
    calc
      _ ≤ (q : ℝ) * (4 * B.card) * (q * B.card) := by gcongr
      _ = _ := by ring
  exact (sq_le_sq₀ (sum_nonneg (by intros; positivity)) (by positivity)).mp (hc.trans hbd)

theorem convolution_fourier {q : ℕ} [NeZero q] (A B : Finset (ZMod q))
    (μ : ZMod q → ℝ) :
    ∑ k : ZMod q, charSum A k * charSum B k * probabilityFourier μ k =
      (q : ℂ) * (∑ a ∈ A, ∑ b ∈ B, (μ (a + b) : ℂ)) := by
  classical
  have horth (a b : ZMod q) :
      (∑ k : ZMod q, ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) *
        probabilityFourier μ k) = (q : ℂ) * μ (a + b) := by
    have hterm (k x : ZMod q) :
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) *
          ((μ x : ℂ) * ZMod.stdAddChar (-(k * x))) =
        (μ x : ℂ) * ZMod.stdAddChar ((a + b - x) * k) := by
      rw [show (a + b - x) * k = k * a + k * b + -(k * x) by ring]
      simp only [AddChar.map_add_eq_mul]
      ring
    simp only [probabilityFourier, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, additive_orthogonality, sub_eq_zero]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  calc
    _ = ∑ k : ZMod q, ∑ a ∈ A, ∑ b ∈ B,
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) * probabilityFourier μ k := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [charSum, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ a ∈ A, ∑ k : ZMod q, ∑ b ∈ B,
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) * probabilityFourier μ k := Finset.sum_comm
    _ = ∑ a ∈ A, ∑ b ∈ B, ∑ k : ZMod q,
        ZMod.stdAddChar (k * a) * ZMod.stdAddChar (k * b) * probabilityFourier μ k := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by simp only [horth, Finset.mul_sum]

theorem convolution_discrepancy {q : ℕ} [NeZero q] (A B I : Finset (ZMod q))
    (μ : ZMod q → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmass : ∑ x, μ x = 1)
    (hsupport : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ I) :
    (A.card : ℝ) * B.card -
        ∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          ‖charSum A k‖ * ‖charSum B k‖ * ‖probabilityFourier μ k‖ ≤
      (q : ℝ) * B.card * ∑ x ∈ I, μ x := by
  classical
  let W : ℝ := ∑ a ∈ A, ∑ b ∈ B, μ (a + b)
  have hW : W ≤ (B.card : ℝ) * ∑ x ∈ I, μ x := by
    dsimp only [W]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ b ∈ B, ∑ x ∈ I, μ x := by
        apply Finset.sum_le_sum
        intro b hb
        calc
          _ = ∑ x ∈ A.image (fun a => a + b), μ x := by
            rw [Finset.sum_image]
            intro a _ a' _ heq
            exact add_right_cancel heq
          _ ≤ ∑ x ∈ I, μ x := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
              exact hsupport a ha b hb
            · intro x _ _
              exact hμ x
      _ = _ := by simp [nsmul_eq_mul]
  have hFourier := convolution_fourier A B μ
  have hzero : charSum A 0 * charSum B 0 * probabilityFourier μ 0 =
      (A.card : ℂ) * B.card := by simp [probabilityFourier_zero μ hmass]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)), hzero] at hFourier
  have hreal : (q : ℝ) * W = (A.card : ℝ) * B.card +
      (∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        charSum A k * charSum B k * probabilityFourier μ k).re := by
    have hh := congrArg Complex.re hFourier
    simpa [W, Complex.mul_re, Complex.mul_im] using hh.symm
  have hn := norm_sum_le ((Finset.univ : Finset (ZMod q)).erase 0)
    (fun k => charSum A k * charSum B k * probabilityFourier μ k)
  simp only [norm_mul] at hn
  have hre := Complex.re_le_norm
    (-(∑ k ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      charSum A k * charSum B k * probabilityFourier μ k))
  simp only [Complex.neg_re, norm_neg] at hre
  have hqW := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ q)
  nlinarith

end ShortEgyptian

end OAI
