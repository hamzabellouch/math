import OAI.Combinatorics.Progressions.Estimates.NormalizedFixedPatchFunction

namespace OAI

section

namespace Erdos3

open scoped NNReal TensorProduct

theorem exists_fixed_patch_niltest_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X Ω T : Type*} [Fintype X] [Fintype Ω] [Nonempty Ω] [Fintype T]
      {d : ℕ} {w : Fin d → ℕ}
      [Fintype (PolynomialShearIndex w)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)],
      ∀ (A : Ω → PolynomialSlots X d w) (Φ : Ω → PatchKernel d)
        (_hw : Monotone w) (_hpos : ∀ i, 1 ≤ w i) (hs : ∀ i, w i ≤ s) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      (∀ a, ((Φ a).lip : ℝ) ≤ Real.exp p) →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights T) (point : Ω → T → X → ℤ)
        (score : Ω → T → ℝ), (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤ (localLaw a).mean (fun t =>
        score a t * ((A a).slots (fun i => (point a t i : ℝ))).patchValue (Φ a))) →
      ∃ (F : (polynomialShearNilmanifold w s hs).Space → ℂ)
        (tests : Ω → (polynomialShearNilmanifold w s hs).Niltest (fun _ : X => 1))
        (retained : Finset Ω),
        (∀ a, (tests a).observable = F ∧ (tests a).UnitIntervalValued ∧
          (tests a).ComplexityLE ((p + 2) ^ C)) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained, Real.exp (-((p + 2) ^ C)) ≤ (localLaw a).mean (fun t =>
          score a t * ((tests a).eval (point a t)).re) := by
  obtain ⟨E, hE, hfixed⟩ := exists_unrestricted_fixed_weight_patch_function s
  obtain ⟨B, hB, hnil⟩ := exists_mass_bounded_patch_niltest_budget s
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ E
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((Q + 2) ^ B + Q)
  refine ⟨C, hC, ?_⟩
  intro X Ω T _ _ _ _ d w _ _ _ _ _ A Φ hw hpos hs p hp hd hX hΦ outer productive localLaw point score hscore hpositive
  let q := (p + 2) ^ E
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by omega)
  have hbudget' : (q + 2) ^ B + q ≤ (p + 2) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by
    have : 0 ≤ (q + 2) ^ B := by positivity
    linarith
  obtain ⟨Ψ, form, localForm, retained, hLip, hMass, hretained, hprob, hlocal⟩ :=
    hfixed A Φ hw hpos hs p hp hd hX hΦ outer productive localLaw point score hscore hpositive
  let P : PolynomialPatch X s d := ⟨w, hpos, hs, hw, form, Ψ⟩
  let M : ℝ≥0 := ⟨q, hq⟩
  have hPm (i) : realPolynomialMass (P.form.center i) ≤ M := hMass i
  have hcomplex := hnil P M hPm q hq (hd.trans hpq) le_rfl hLip
  have hcomplex' : (P.shearNiltest M hPm).ComplexityLE ((p + 2) ^ C) :=
    hcomplex.mono (by linarith)
  obtain ⟨F, tests, htests, heval⟩ := P.exists_fixed_observable_family M hPm localForm hcomplex'
  refine ⟨F, tests, retained, htests, hretained, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (outer.mass_nonneg productive)).trans hprob
  · intro a ha
    have h := (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hlocal a ha)
    simp_rw [heval]
    exact h

end Erdos3

end

end OAI
