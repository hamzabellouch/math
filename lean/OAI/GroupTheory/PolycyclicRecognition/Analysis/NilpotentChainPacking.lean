import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! # Polynomial packing of nilpotent chains

The logarithmic endpoint estimate and exponential-coordinate Haar formula
supply actual finite polynomial bounds on separated chains. Only the precise
published nilpotent exponential inputs are used.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule MeasureTheory Metric
open scoped Manifold ENNReal

variable {G : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G] [ProperSpace G]

/-- A fixed positive ball mass converts a real volume coefficient into a
natural cardinal coefficient, uniformly in the scale. -/
theorem exists_card_coefficient_of_haar_volume
    (μ : Measure G) [μ.IsHaarMeasure] {r F : ℝ} (hr : 0 < r)
    (b : ℕ) (region : ℕ → Set G)
    (hvol : ∀ n, μ (region n) ≤ ENNReal.ofReal F * (1 + (n : ℝ≥0∞)) ^ b) :
    ∃ C : ℕ, ∀ (n : ℕ) (s : Finset G),
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r + r ≤ dist x y) →
      (∀ x ∈ s, ball x r ⊆ region n) → s.card ≤ C * (1 + n) ^ b := by
  let q := μ (ball (1 : G) r)
  have hq0 : q ≠ 0 := (measure_ball_pos μ (1 : G) hr).ne'
  have hqtop : q ≠ ∞ := measure_ball_ne_top
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  let C : ℕ := ⌈F / q.toReal⌉₊
  have hcoef : ENNReal.ofReal F ≤ (C : ℝ≥0∞) * q := by
    have h : F ≤ (C : ℝ) * q.toReal :=
      (div_le_iff₀ hqpos).mp (Nat.le_ceil (F / q.toReal))
    have hh := ENNReal.ofReal_le_ofReal h
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg C), ENNReal.ofReal_natCast,
      ENNReal.ofReal_toReal hqtop] using hh
  refine ⟨C, ?_⟩
  intro n s hsep hthick
  apply separated_card_le_polynomial μ s r (region n) C b n hq0 hqtop hsep hthick
  have hh := (hvol n).trans (mul_le_mul' hcoef le_rfl)
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    mul_assoc, mul_left_comm, mul_comm] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [SimplyConnectedSpace G] [DecidableEq G]

/-- Nilpotent chains satisfy the required finite polynomial packing property.
This applies to any height map, since the estimate uses just the steps. -/
theorem polynomialBoundedChainPacking_of_nilpotent_exponential
    (dynkin : NilpotentDynkinExpansionInput E G)
    (haarInput : NilpotentExponentialHaarInput E G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {W : Type*} [NormedAddCommGroup W] (π : G → W) :
    PolynomialBoundedChainPacking π := by
  classical
  let b := Module.finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  obtain ⟨chart, μ, hchart, hμ, hvol⟩ := exists_haar_exponential_cube_volume haarInput Exp hExp hnil b
  let := hμ
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ
    (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G)).mp hnil
  intro x L M hL hM
  obtain ⟨A, hA, hcoord⟩ := exists_polynomial_chain_coordinate_bound (W := ℝ)
    dynkin Exp hExp chart hchart hc b (max L 1)
  let D : ℝ := A * 2 ^ c
  have hD : 0 ≤ D := by positivity
  let radius : ℕ → ℝ := fun n => D * (1 + (n : ℝ)) ^ c
  have hradius (n : ℕ) : 0 ≤ radius n := by dsimp [radius]; positivity
  let region : ℕ → Set G := fun n =>
    (fun y => x⁻¹ * y) ⁻¹' exponentialCoordinateBox Exp b (radius n)
  let S : ℕ → Set G := fun n => {y | ∃ m ≤ n, BoundedHeightChain π L M m x y}
  have hthick (n : ℕ) (y : G) (hy : y ∈ S n) : ball y (1 / 2 : ℝ) ⊆ region n := by
    obtain ⟨m, hm, hchain⟩ := hy
    intro z hz
    have hz' : dist y z ≤ max L 1 := by
      have hh : dist z y < 1 / 2 := hz
      rw [dist_comm] at hh
      linarith [le_max_right L (1 : ℝ)]
    have hchain' : BoundedHeightChain (fun _ : G => (0 : ℝ)) (max L 1) 0 m x y :=
      (hchain.mono_step (le_max_left L 1)).change_height (by intro u hu; simp)
    obtain ⟨v, hv, hbound⟩ := hcoord (fun _ : G => (0 : ℝ)) 0 (m + 1) x z
      (hchain'.snoc (by simp) hz')
    refine ⟨v, hv, hbound.trans ?_⟩
    change A * (1 + ((m + 1 : ℕ) : ℝ)) ^ c ≤ D * (1 + (n : ℝ)) ^ c
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ((m + 1 : ℕ) : ℝ))
      (show 1 + ((m + 1 : ℕ) : ℝ) ≤ 2 * (1 + (n : ℝ)) by push_cast; linarith) c
    have hh := mul_le_mul_of_nonneg_left hp hA
    simpa only [mul_pow, D, mul_assoc] using hh
  let F : ℝ := (2 * D) ^ finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  have hF : 0 ≤ F := by positivity
  have hregion (n : ℕ) : μ (region n) ≤
      ENNReal.ofReal F * (1 + (n : ℝ≥0∞)) ^ (c * finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
    dsimp only [region]
    rw [measure_preimage_mul, hvol _ (hradius n)]
    have hpow : (2 * radius n) ^ finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G) =
        F * (1 + (n : ℝ)) ^ (c * finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) := by
      dsimp [radius, F]
      rw [← mul_assoc, mul_pow, ← pow_mul]
    rw [← ENNReal.ofReal_pow (hradius n |> mul_nonneg (by norm_num)), hpow,
      ENNReal.ofReal_mul hF]
    simp only [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 + n),
      ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg n), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, le_refl]
  obtain ⟨C, hcard⟩ := exists_card_coefficient_of_haar_volume μ (by norm_num : (0 : ℝ) < 1 / 2)
    (c * finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) region hregion
  have hnet (n : ℕ) := finite_cover_set_of_separated_bound (S n) (by norm_num : (0 : ℝ) ≤ 1)
    (C * (1 + n) ^ (c * finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))) (by
      intro s hs hsep
      apply hcard n s
      · intro y hy z hz hyz
        have := hsep y hy z hz hyz
        linarith
      · exact fun y hy => hthick n y (hs hy))
  choose centers hcenters hcounts hcover using hnet
  exact ⟨C, c * finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G), centers, hcounts,
    fun n m hm y hy => hcover n y ⟨m, hm, hy⟩⟩

end PolycyclicRecognition

end

end OAI
