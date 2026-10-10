import OAI.Combinatorics.Progressions.Nilpotent.MajorTranslationRationalLiftNiltest
import OAI.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module VectorPolynomial
open scoped TensorProduct NNReal BigOperators

theorem exists_tagged_major_fourier_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (J : Fin m → Type*) [∀ j, Fintype (J j)]
      [Fintype (WeightedBasisIndex (lowTaggedWeight J d) d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra (lowTaggedWeight J d) d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra (lowTaggedWeight J d) d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra (lowTaggedWeight J d) d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra (lowTaggedWeight J d) d)]
      (_hd : 0 < d) (cover : ℕ) (hcover : 0 < cover)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (D : MvPolynomial (U ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) (lowTaggedWeight J d)) d)
      (poly : ∀ j, VectorPolynomial U ℝ (J j → ℝ))
      (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) (a : (Σ j, J j) → ℤ)
      (_hann : ∀ j, d < j.val + 1 →
        W j ≤ LinearMap.ker (integerRowLinear (fun i => a ⟨j, i⟩)))
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + Fintype.card (Σ j, J j) : ℕ) ≤ p)
      (_hcoverp : (cover : ℝ) ≤ Real.exp p) (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p)
      (_ha : ∀ i, |(a i : ℝ)| ≤ Real.exp p),
      ∃ F : (weightedTranslationResidueNilmanifold (lowTaggedWeight J d) d
          (lowTaggedWeight_pos J d) (lowTaggedWeight_le J d) cover hcover).Niltest
          (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit (lowTaggedWeight J d) d
          (lowTaggedWeight_pos J d) (lowTaggedWeight_le J d)
          (fractionalCoefficientPolynomial D)
          (fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
            (Sum.elim (fun _ : U => 1) (lowTaggedWeight J d)) d hD
              (mem_support_iff.mp hα)).le)
          (fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
          (fun i => (MvPolynomial.totalDegree_sub_C_le _ _).trans
            (lowTaggedPolynomial_degree J d poly hpoly i)) ∧
        ∀ u : U → ℤ,
          F.eval u =
            (Ψ.value (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
                (lowTaggedPolynomial J d poly i) - c i -
                (nearestLowCoordinateLift (lowTaggedPolynomial J d poly) c u i : ℝ)) : ℂ) *
              (Real.fourierChar (MvPolynomial.eval (fun j =>
                ((Sum.elim u (nearestLowCoordinateLift (lowTaggedPolynomial J d poly) c u)
                  j : ℤ) : ℝ)) D) : ℂ) *
              (Real.fourierChar (MvPolynomial.eval (fun j => (u j : ℝ))
                (normalizedTwistFrequencyPolynomial cover a poly)) : ℂ) := by
  obtain ⟨C, hC, hmain⟩ := exists_majorTranslation_rationalLift_niltest_nearest d
  refine ⟨C, hC, ?_⟩
  intro U _ m J _ _ _ _ _ _ hd cover hcover Ψ D hD poly hpoly W hcoeff c a hann p hp
    hdim hcoverp hΨ ha
  have hlowdim : ((Fintype.card U + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Nat.add_le_add_left (lowTaggedIndex_card_le J d) _)).trans hdim
  obtain ⟨F, hnorm, hcomp, horbit, heval⟩ := hmain (lowTaggedWeight J d)
    (lowTaggedWeight_pos J d) (lowTaggedWeight_le J d) hd cover hcover Ψ D hD
    (lowTaggedPolynomial J d poly) (lowTaggedPolynomial_degree J d poly hpoly)
    c (lowTaggedFrequency J d a) hp hlowdim hcoverp hΨ
    (lowTaggedFrequency_bound J d a _ ha)
  let k := normalizedTwistHighFrequencyConstant cover d a poly
  refine ⟨F.phaseShift k, by simpa using hnorm, by simpa using hcomp, horbit, ?_⟩
  intro u
  rw [RationalFilteredNilmanifold.Niltest.phaseShift_eval, heval]
  rw [normalizedTwistFrequencyPolynomial_low_add_constant cover d W a poly hcoeff hann,
    map_add, eval_C, normalizedTwistFrequencyPolynomial_low_eval]
  rw [Real.fourierChar.map_add_eq_mul, Circle.coe_mul]
  dsimp only [k]
  ring

end Erdos3.PolynomialTranslationLie

end

end OAI
