import OAI.GroupTheory.PolycyclicRecognition.Algebra.RegularWalkEnergyLowerBound
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialEnergyScales
import OAI.GroupTheory.PolycyclicRecognition.Analysis.UnitaryApproximateHarmonic

namespace OAI

/-! # A nonconstant linear-growth harmonic function under polynomial growth

The regular lazy walk has polynomially bounded-below energy. Energy descent
therefore supplies normalized coboundaries with vanishing harmonic defect.
Scalar projection and pointwise compactness complete the construction.
-/
noncomputable section
namespace PolycyclicRecognition
open Filter Finset
open scoped Topology
variable {G : Type*} [Group G] [DecidableEq G] [Infinite G]

theorem regularLazyWalk_small_laplacian
    (S : Finset G) (hne : S.Nonempty) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    {C : ℝ} (hC : 0 < C) (b : ℕ)
    (hvol : ∀ n, ((wordBall S n).card : ℝ) ≤ C * (1 + (n : ℝ)) ^ b)
    {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ,
      0 < unitaryCocycleEnergy S
        (unitaryCoboundary regularHilbertRepresentation (regularLazyWalk S n)) ∧
      ‖unitaryGeneratorLaplacian S regularHilbertRepresentation (regularLazyWalk S n)‖ /
        Real.sqrt (unitaryCocycleEnergy S
          (unitaryCoboundary regularHilbertRepresentation (regularLazyWalk S n))) ≤ δ := by
  let e (n : ℕ) := unitaryCocycleEnergy S
    (unitaryCoboundary regularHilbertRepresentation (regularLazyWalk S n))
  have hK : 0 < 4 * C ^ 2 := by positivity
  have hlower (n : ℕ) : 1 / (4 * C ^ 2) ≤ (1 + (n : ℝ)) ^ (2 * (b + 1)) * e n := by
    apply (div_le_iff₀ hK).mpr
    have h := regularLazyWalk_polynomial_energy_lower S hne hS hgen hC.le b hvol n
    simpa only [e, mul_assoc, mul_left_comm, mul_comm] using h
  have he (n : ℕ) : 0 < e n := by
    have hh := lt_of_lt_of_le (by positivity : 0 < 1 / (4 * C ^ 2)) (hlower n)
    exact pos_of_mul_pos_right hh (by positivity)
  have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hne)
  obtain ⟨n, _, hn⟩ := exists_small_relative_energy_drop e (fun n => (he n).le)
    (by positivity : 0 < 1 / (4 * C ^ 2)) (2 * (b + 1)) hlower
    (by positivity : 0 < δ ^ 2 / (S.card : ℝ)) 0
  refine ⟨n, he n, ?_⟩
  have hdesc := unitaryLazyStep_energy_descent S hS hne
    regularHilbertRepresentation (regularLazyWalk S n)
  change _ ≤ e n - e (n + 1) at hdesc
  have hsq : ‖unitaryGeneratorLaplacian S regularHilbertRepresentation
      (regularLazyWalk S n)‖ ^ 2 ≤ δ ^ 2 * e n := by
    calc
      _ ≤ (δ ^ 2 / (S.card : ℝ) * e n) * S.card :=
        (div_le_iff₀ hm).mp (hdesc.trans hn)
      _ = _ := by field_simp
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (he n))).mpr
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ.le (Real.sqrt_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt (he n).le] using hsq

theorem polynomial_growth_nonconstant_harmonic
    (S : Finset G) (hne : S.Nonempty) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    {C : ℝ} (hC : 0 < C) (b : ℕ)
    (hvol : ∀ n, ((wordBall S n).card : ℝ) ≤ C * (1 + (n : ℝ)) ^ b) :
    ∃ F : polynomialHarmonicFunctions S 1, ∃ s ∈ S, F.val s ≠ F.val 1 := by
  have hex (k : ℕ) := regularLazyWalk_small_laplacian S hne hS hgen hC b hvol
    (by positivity : 0 < 1 / ((k : ℝ) + 1))
  choose n hn hsmall using hex
  let v (k : ℕ) := regularLazyWalk S (n k)
  apply nonconstant_harmonic_of_almost_harmonic_cocycles (l := atTop)
    S hne hS hgen (fun _ : ℕ => regularHilbertRepresentation)
    (fun k => unitaryCoboundary regularHilbertRepresentation (v k))
    (fun _ => unitaryCoboundary_isCocycle _ _) hn
  simp only [unitaryCoboundary_sum, norm_neg]
  apply squeeze_zero (fun _ => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    hsmall tendsto_one_div_add_atTop_nhds_zero_nat

theorem polynomial_growth_harmonic_representation_infinite
    (S : Finset G) (hne : S.Nonempty) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    {C : ℝ} (hC : 0 < C) (b : ℕ)
    (hvol : ∀ n, ((wordBall S n).card : ℝ) ≤ C * (1 + (n : ℝ)) ^ b) :
    (Set.range (polynomialHarmonicRepresentation S hS hgen 1)).Infinite := by
  obtain ⟨F, s, _, hs⟩ := polynomial_growth_nonconstant_harmonic S hne hS hgen hC b hvol
  exact polynomialHarmonicRepresentation_infinite_range S hS hgen 1 F s hs

end PolycyclicRecognition

end

end OAI
