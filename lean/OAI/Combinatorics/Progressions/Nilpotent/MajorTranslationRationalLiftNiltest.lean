import OAI.Combinatorics.Progressions.Nilpotent.CanonicalReducedMajorTwistedNiltest

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped NNReal TensorProduct BigOperators

noncomputable def nearestLowCoordinateLift {U : Type*} {m : ℕ}
    (L : Fin m → MvPolynomial U ℝ) (c : Fin m → ℝ) (u : U → ℤ) : Fin m → ℤ :=
  nearestIntegerLift (fun i => eval (fun j => (u j : ℝ)) (L i) - c i)

theorem nearestLowCoordinateLift_close {U : Type*} {m : ℕ}
    (L : Fin m → MvPolynomial U ℝ) (c : Fin m → ℝ) (u : U → ℤ) (i : Fin m) :
    |eval (fun j => (u j : ℝ)) (L i) - c i - (nearestLowCoordinateLift L c u i : ℝ)| ≤ 1 / 2 :=
  nearestIntegerLift_close (fun j => eval (fun k => (u k : ℝ)) (L j) - c j) i

theorem exists_majorTranslation_rationalLift_niltest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
      (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (L : Fin m → MvPolynomial U ℝ) (hL : ∀ i, (L i).totalDegree ≤ w i)
      (c : Fin m → ℝ) (a : Fin m → ℤ)
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hMp : (M : ℝ) ≤ Real.exp p) (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p)
      (_ha : ∀ i, |(a i : ℝ)| ≤ Real.exp p),
      ∃ F : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
            (Sum.elim (fun _ : U => 1) w) d hD (mem_support_iff.mp hα)).le)
          (fun i => L i - MvPolynomial.C (c i))
          (fun i => (MvPolynomial.totalDegree_sub_C_le (L i) (c i)).trans (hL i)) ∧
        ∀ u : U → ℤ, ∀ β : Fin m → ℤ,
          (∀ i, |eval (fun j => (u j : ℝ)) (L i) - c i - (β i : ℝ)| ≤ 1 / 2) →
          F.eval u =
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (L i) - c i - (β i : ℝ)) : ℂ) *
              (Real.fourierChar (eval (fun j => ((Sum.elim u β j : ℤ) : ℝ)) D) : ℂ) *
              (Real.fourierChar ((∑ i, (a i : ℝ) * eval (fun j => (u j : ℝ)) (L i)) / (M : ℝ)) : ℂ) := by
  obtain ⟨b, _, htwisted⟩ := exists_majorTranslation_reduced_twisted_niltest d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (2 * X + 8 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd M hM Ψ D hD L hL c a p hp hdim hMp hΨ ha
  let A : Fin m → MvPolynomial U ℝ := fun i => L i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i :=
    fun i => (MvPolynomial.totalDegree_sub_C_le (L i) (c i)).trans (hL i)
  let q : ℝ := 2 * p + 8
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hm : (m : ℝ) ≤ p := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by
      exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans hdim
  have hK : (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp q := by
    have hpi : 2 * Real.pi ≤ Real.exp (8 : ℝ) := by
      linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
    have hmexp : (m : ℝ) ≤ Real.exp p := hm.trans (by linarith [Real.add_one_le_exp p])
    calc
      _ ≤ 2 * Real.pi * m * Real.exp p := rationalLiftCharacterTwistLip_le M hM a _ ha
      _ ≤ Real.exp 8 * Real.exp p * Real.exp p := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg p)
        exact mul_le_mul hpi hmexp (Nat.cast_nonneg m) (Real.exp_nonneg 8)
      _ = Real.exp q := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [q]
        ring
  obtain ⟨F, hnorm, hcomp, horbit, heval⟩ := htwisted w hw hwd hd M hM Ψ D hD A hA
    (rationalLiftCharacterTwistLip M a) (rationalLiftCharacterTwist M a c)
    (fun x r => (rationalLiftCharacterTwist_norm M a c x r).le)
    (rationalLiftCharacterTwist_lipschitz M a c) hq (hdim.trans hpq)
    (hMp.trans (Real.exp_le_exp.mpr hpq)) (hΨ.trans (Real.exp_le_exp.mpr hpq)) hK
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨F, hnorm, hcomp.mono hcost, horbit, ?_⟩
  intro u β hβ
  have hβ' : ∀ i, |eval (fun j => (u j : ℝ)) (A i) - (β i : ℝ)| ≤ 1 / 2 := by
    simpa only [A, map_sub, eval_C] using hβ
  rw [heval u β hβ', rationalLiftCharacterTwist_residual M hM]
  simp only [A, map_sub, eval_C, sub_add_cancel]
  ring

theorem exists_majorTranslation_rationalLift_niltest_nearest (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (_hd : 0 < d) (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m)
      (D : MvPolynomial (U ⊕ Fin m) ℝ)
      (hD : D.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (L : Fin m → MvPolynomial U ℝ) (hL : ∀ i, (L i).totalDegree ≤ w i)
      (c : Fin m → ℝ) (a : Fin m → ℤ)
      {p : ℝ} (_hp : 0 ≤ p) (_hdim : (Fintype.card U + m : ℕ) ≤ p)
      (_hMp : (M : ℝ) ≤ Real.exp p) (_hΨ : (Ψ.lip : ℝ) ≤ Real.exp p)
      (_ha : ∀ i, |(a i : ℝ)| ≤ Real.exp p),
      ∃ F : (weightedTranslationResidueNilmanifold w d hw hwd M hM).Niltest (fun _ : U => 1),
        F.normBound = 1 ∧ F.ComplexityLE ((p + C) ^ C) ∧
        F.orbit = majorTranslationPolynomialOrbit w d hw hwd
          (fractionalCoefficientPolynomial D)
          (fun _ hα => (fractionalCoefficientPolynomial_isWeightedHomogeneous D
            (Sum.elim (fun _ : U => 1) w) d hD (mem_support_iff.mp hα)).le)
          (fun i => L i - MvPolynomial.C (c i))
          (fun i => (MvPolynomial.totalDegree_sub_C_le (L i) (c i)).trans (hL i)) ∧
        ∀ u : U → ℤ,
          F.eval u =
            (Ψ.value (fun i => eval (fun j => (u j : ℝ)) (L i) - c i -
              (nearestLowCoordinateLift L c u i : ℝ)) : ℂ) *
              (Real.fourierChar (eval
                (fun j => ((Sum.elim u (nearestLowCoordinateLift L c u) j : ℤ) : ℝ)) D) : ℂ) *
              (Real.fourierChar ((∑ i, (a i : ℝ) * eval (fun j => (u j : ℝ)) (L i)) / (M : ℝ)) : ℂ) := by
  obtain ⟨C, hC, hmain⟩ := exists_majorTranslation_rationalLift_niltest d
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ _ _ _ _ hd M hM Ψ D hD L hL c a p hp hdim hMp hΨ ha
  obtain ⟨F, hnorm, hcomp, horbit, heval⟩ :=
    hmain w hw hwd hd M hM Ψ D hD L hL c a hp hdim hMp hΨ ha
  exact ⟨F, hnorm, hcomp, horbit, fun u => heval u (nearestLowCoordinateLift L c u)
    (nearestLowCoordinateLift_close L c u)⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
