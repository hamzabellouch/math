import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateConjugationDecay
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledWordSums

namespace OAI

/-! # Interior slack from actual finite word coefficients

A larger choice of the manuscript's free interior constant lets the
uniform nilpotent operator estimate absorb the enlarged suffix. No
coordinate growth estimate is assumed: both estimates follow from the
finite word expansions and maximizing-basis exchange.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology BigOperators

variable {I L G A : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The logarithm of the conjugate tends to zero in every maximizing
rescaled basis. This applies to the actual exponential product through
the faithful realization, with no new conjugation identity assumed. -/
theorem rescaled_word_conjugation_tendsto_zero
    [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {m k₀ c₀ : ℕ}
    (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hnil : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ)
    (β : ℝ → WordBasisSelections X (boundedBracketWords k₀))
    (hβ : ∀ r, IsMaximizingColumnBasis
      (wordListCoordinates X (boundedBracketWords k₀) b₀)
      (fun w => bracketWordExponent s w) (β r).val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {δ c lo hi K U : ℝ}
    (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (m : ℝ) * hi < c * lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (k u : ℝ → boundedBracketWords (I := I) k₀ → ℝ)
    (hkcoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |k r w| ≤ K * Real.exp (r * ((1 + δ) * bracketWordExponent s w + ε r)))
    (hucoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |u r w| ≤ U * Real.exp (r * ((1 - c * δ) * bracketWordExponent s w + ε r))) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
      (fun i => bracketWordExponent s ((β r).val i)) r
    let x := fun r => (b r).equivFun
      (∑ w, k r w • evalBracketWord X w)
    let y := fun r => (b r).equivFun
      (∑ w, u r w • evalBracketWord X w)
    Tendsto (fun r => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) (x r) (y r)) (-(x r))) atTop (𝓝 0) := by
  let S := boundedBracketWords (I := I) k₀
  let cost : S → ℝ := fun w => bracketWordExponent s w
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S (β r))
    (fun i => cost ((β r).val i)) r
  let x := fun r => (b r).equivFun (∑ w : S, k r w • evalBracketWord X w)
  let y := fun r => (b r).equivFun (∑ w : S, u r w • evalBracketWord X w)
  change Tendsto (fun r => dynkinProduct a (basisBracket (b r))
    (dynkinProduct a (basisBracket (b r)) (x r) (y r)) (-(x r))) atTop (𝓝 0)
  obtain ⟨C, hC, hword⟩ := exists_uniform_rescaled_word_bound X S b₀
  obtain ⟨D, hD, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound X hk b₀
  have hbnd : ∀ᶠ r : ℝ in atTop,
      ‖basisBracket (b r)‖ ≤ (finrank ℝ L : ℝ) ^ 2 * D := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact norm_basisBracket_le (b r) hD (hbracket s (β r) (hβ r) r hr)
  have hx : ∀ᶠ r : ℝ in atTop, ‖x r‖ ≤
      ((Fintype.card S : ℝ) * C * K) * Real.exp ((δ * hi + ε r) * r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hkcoeff] with r hr hkr
    have he (w : S) : |k r w| ≤ K * Real.exp (r * (cost w + (δ * hi + ε r))) := by
      apply (hkr w).trans
      apply mul_le_mul_of_nonneg_left _ hK
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hr
      have ht := mul_le_mul_of_nonneg_left (hcost w).2 hδ.le
      dsimp [cost]
      nlinarith
    have ht := norm_rescaled_word_sum_le X S (b r) cost r hK
      (hword cost (β r) (hβ r) r hr) id (k r) he
    simpa only [x, id_eq, mul_comm r] using ht
  have hy : ∀ᶠ r : ℝ in atTop, ‖y r‖ ≤
      ((Fintype.card S : ℝ) * C * U) * Real.exp ((-(c * δ * lo) + ε r) * r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hucoeff] with r hr hur
    have he (w : S) : |u r w| ≤ U * Real.exp (r * (cost w + (-(c * δ * lo) + ε r))) := by
      apply (hur w).trans
      apply mul_le_mul_of_nonneg_left _ hU
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hr
      have ht := mul_le_mul_of_nonneg_left (hcost w).1 (mul_nonneg hc hδ.le)
      dsimp [cost]
      nlinarith
    have ht := norm_rescaled_word_sum_le X S (b r) cost r hU
      (hword cost (β r) (hβ r) r hr) id (u r) he
    simpa only [y, id_eq, mul_comm r] using ht
  have hgap' : (m : ℝ) * (δ * hi) < c * δ * lo := by
    have ht := mul_lt_mul_of_pos_left hgap hδ
    nlinarith
  exact coordinate_conjugation_tendsto_zero b hnil a
    (fun r => basis_exponentialConjugationLaw (b r) Exp hinj hneg a hm j ρ hρ hmatch)
    x y (mul_nonneg (sq_nonneg _) hD)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hK)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) hU)
    (mul_nonneg hδ.le hhi) hbnd hgap' ε hε hx hy

end PolycyclicRecognition

end

end OAI
