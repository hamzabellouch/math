import OAI.Combinatorics.Progressions.Fourier.NormalizedTwistLocalizedFourierSelection
import OAI.Combinatorics.Progressions.Polynomial.OrdinaryPolynomialPhaseAffineInverse

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_normalizedTwist_high_frequency_removal (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (d : ℕ)
      (D : RationalFilteredNilmanifold L t e) (_htd : t ≤ d)
      (R : D.Niltest (fun _ : X => 1))
      (cover : ℕ) (_hcover : 0 < cover) (a : (Σ j, J j) → ℤ)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      (cover : ℝ) ≤ Real.exp p → (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, d < j.val + 1 → HasLayerSamplingRank (j.val + 1)
        (fun i => (lengths i : ℝ)) Rrank (W j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        (Real.fourierChar (MvPolynomial.eval (fun i => (x i : ℝ))
          (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) * R.eval x‖ →
      ∀ j, d < j.val + 1 → W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)) := by
  classical
  choose c hc hinverse using fun j : Fin m =>
    OrdinaryPolynomialPhase.exists_ordinary_polynomial_phase_inverse (j.val + 1)
      (Nat.succ_pos _)
  let B := (∑ j, c j) + 2
  have hcB (j : Fin m) : c j ≤ B :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Nat.le_add_right _ _)
  have hB : 2 ≤ B := by dsimp [B]; omega
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ d D htd R cover hcover a poly hpoly W hcoeff p Rrank hp
    hR hRcap hcoverp ha origin lengths hlengths hX hlarge hRrank hrank hcorr
  have hT : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  have hbudget' : p + (p + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hbase : 1 ≤ p + B := by
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hlocal (j : Fin m) : (p + c j) ^ c j ≤ (p + B) ^ B := by
    have hb : p + (c j : ℝ) ≤ p + B := by
      have hh : (c j : ℝ) ≤ B := Nat.cast_le.mpr (hcB j)
      linarith
    apply (pow_le_pow_left₀ (by positivity) hb _).trans
    exact pow_le_pow_right₀ hbase (hcB j)
  rcases highest_nonannihilating_tag d W a with hann | ⟨h, hd, hw, hhigher⟩
  · exact hann
  · exfalso
    have hhigh (j : Fin m) (hj : h < j) :
        integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j) =
          MvPolynomial.C ((integerRowPolynomial (fun i => a ⟨j, i⟩) (poly j)).coeff 0) :=
      integerRowPolynomial_constant_of_annihilates (W j) _ _ (hcoeff j) (hhigher j hj)
    have hdegree (j : Fin m) := integerRowPolynomial_totalDegree_le
      (fun i => a ⟨j, i⟩) (hpoly j)
    have hphase : (normalizedTwistFrequencyPolynomial cover a poly).totalDegree ≤ h.val + 1 := by
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      exact taggedScalar_sum_degree h _ hdegree hhigh
    have htop : homogeneousComponent (h.val + 1) (normalizedTwistFrequencyPolynomial cover a poly) =
        MvPolynomial.C (1 / (cover : ℝ)) * homogeneousComponent (h.val + 1)
          (integerRowPolynomial (fun i => a ⟨h, i⟩) (poly h)) := by
      rw [normalizedTwistFrequencyPolynomial, homogeneousComponent_C_mul,
        taggedScalar_sum_top h _ hdegree hhigh]
    have hcost : p + (p + c h) ^ c h ≤ (p + C) ^ C := by linarith [hlocal h]
    have hap := hinverse h D (by omega) (normalizedTwistFrequencyPolynomial cover a poly)
      hphase R p hp hR hRcap origin lengths hlengths hX
      (fun i => (Real.exp_le_exp.mpr (by linarith : (p + c h) ^ c h ≤ (p + C) ^ C)).trans
        (hlarge i)) hcorr
    apply normalizedTwistFrequencyPolynomial_top_not_approximation cover hcover h a poly
      (W h) (fun i => (lengths i : ℝ)) Rrank (Real.exp ((p + c h) ^ c h)) hT
      ?_ (hrank h hd) ?_ hw htop hap
    · calc
        _ ≤ Real.exp p * Real.exp ((p + c h) ^ c h) :=
          mul_le_mul_of_nonneg_right hcoverp (Real.exp_nonneg _)
        _ = Real.exp (p + (p + c h) ^ c h) := (Real.exp_add _ _).symm
        _ ≤ Rrank := (Real.exp_le_exp.mpr hcost).trans hRrank
    · intro i
      exact (ha ⟨h, i⟩).trans ((Real.exp_le_exp.mpr
        (by linarith [pow_nonneg (show 0 ≤ p + B by positivity) B] : p ≤ (p + C) ^ C)).trans hRrank)

end Erdos3.VectorPolynomial

end

end OAI
