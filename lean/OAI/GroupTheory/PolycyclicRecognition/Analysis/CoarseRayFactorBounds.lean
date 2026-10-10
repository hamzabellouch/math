import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseNegativeQuotient

namespace OAI

/-! # Uniform factor bounds along centered coarse rays -/

noncomputable section
namespace PolycyclicRecognition

/-- A common sublinear height estimate makes every centered coarse ray
uniformly negative after one shift. Actual metric factorization then gives
uniform polynomial Cartan coordinates and bounded relative increments. -/
theorem centered_coarse_ray_factor_bounds
    {P S N D G : Type*} [MetricSpace S] [One S]
    [Group N] [Group D] [Group G] [MetricSpace G] [IsIsometricSMul G G]
    (ι : N →* G) (κ : D →* G) (size height : D → ℝ)
    (sourceHeight : S → ℝ) (targetHeight : G → ℝ)
    (f : P → S → G) (hcenter : ∀ p, f p 1 = 1)
    {L error R gap step B : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hgap : 0 < gap) (hB : 0 ≤ B)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ p x,
      |targetHeight (f p x) - sourceHeight x| ≤ ε * dist 1 x + C)
    (ray : ℕ → S) (hray : ∀ n, dist 1 (ray n) ≤ R * n)
    (hnegative : ∀ n, sourceHeight (ray n) ≤ -gap * n)
    (hstep : ∀ n, dist (ray n) (ray (n + 1)) ≤ step)
    (degree : ℕ)
    (hfactor : ∀ g : G, ∃ u d, ι u * κ d = g ∧ 0 ≤ size d ∧
      size d ≤ B * (3 + dist 1 g) ^ degree ∧ height d = targetHeight g) :
    ∃ (n₀ : ℕ) (C : ℝ), 0 ≤ C ∧ ∃ (u : P → ℕ → N) (d : P → ℕ → D),
      (∀ p n, ι (u p n) * κ (d p n) = f p (ray (n + n₀)) ∧
        0 ≤ size (d p n) ∧ size (d p n) ≤ C * (1 + (n : ℝ)) ^ degree ∧
        height (d p n) ≤ -(gap / 2) * n) ∧
      ∀ p n, dist (f p (ray (n + n₀))) (f p (ray (n + 1 + n₀))) ≤ L * step + error := by
  classical
  have hs : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : P × S,
      ‖targetHeight (f z.1 z.2) - sourceHeight z.2‖ ≤ ε * dist 1 z.2 + C := by
    intro ε hε
    obtain ⟨C, hC, hc⟩ := hsub ε hε
    exact ⟨C, hC, fun z => by simpa only [Real.norm_eq_abs] using hc z.1 z.2⟩
  obtain ⟨r₀, _, hsmall⟩ := uniform_sublinear_on_balls (fun z : P × S => dist 1 z.2)
    hs hR (gap / 2) (half_pos hgap)
  let n₀ := ⌈r₀⌉₊
  have hn₀ : r₀ ≤ (n₀ : ℝ) := Nat.le_ceil r₀
  let T := 3 + L * R * (n₀ + 1) + |error|
  have hT : 0 ≤ T := by dsimp [T]; positivity
  choose u d hd using fun p n => hfactor (f p (ray (n + n₀)))
  refine ⟨n₀, B * T ^ degree, by positivity, u, d, ?_, ?_⟩
  · intro p n
    obtain ⟨he, h0, hb, hh⟩ := hd p n
    refine ⟨he, h0, hb.trans ?_, ?_⟩
    · have hdist : dist 1 (f p (ray (n + n₀))) ≤ L * (R * (n + n₀)) + error := by
        have hl := hf p 1 (ray (n + n₀))
        rw [hcenter] at hl
        have hh := hl.trans (add_le_add (mul_le_mul_of_nonneg_left (hray (n + n₀)) hL) (le_refl error))
        simpa only [Nat.cast_add] using hh
      have ht : 3 + dist 1 (f p (ray (n + n₀))) ≤ T * (1 + (n : ℝ)) := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hn₀' : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
        have hLR := mul_nonneg hL hR
        have hcross := mul_nonneg hLR (mul_nonneg hn₀' hn)
        have he' := le_abs_self error
        change 3 + dist 1 (f p (ray (n + n₀))) ≤
          (3 + L * R * ((n₀ : ℝ) + 1) + |error|) * (1 + n)
        nlinarith [abs_nonneg error]
      calc
        B * (3 + dist 1 (f p (ray (n + n₀)))) ^ degree ≤
            B * (T * (1 + (n : ℝ))) ^ degree := by gcongr
        _ = (B * T ^ degree) * (1 + (n : ℝ)) ^ degree := by rw [mul_pow]; ring
    · rw [hh]
      have hn : r₀ ≤ ((n + n₀ : ℕ) : ℝ) := hn₀.trans (by exact_mod_cast Nat.le_add_left n₀ n)
      have herr := hsmall ((n + n₀ : ℕ) : ℝ) hn (p, ray (n + n₀)) (hray (n + n₀))
      rw [Real.norm_eq_abs] at herr
      have hupper := le_abs_self (targetHeight (f p (ray (n + n₀))) - sourceHeight (ray (n + n₀)))
      have hneg := hnegative (n + n₀)
      push_cast at herr hneg
      nlinarith [Nat.cast_nonneg (α := ℝ) n₀]
  · intro p n
    have hs' : dist (ray (n + n₀)) (ray (n + 1 + n₀)) ≤ step := by
      simpa only [Nat.add_right_comm n 1 n₀] using hstep (n + n₀)
    exact (hf p _ _).trans (add_le_add (mul_le_mul_of_nonneg_left hs' hL) (le_refl error))

end PolycyclicRecognition

end

end OAI
