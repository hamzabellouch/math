import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateBoundedInverse

namespace OAI

/-! # Continuous endpoint coding in actual rescaled Lie coordinates

The compact normalized laws give a common coordinate ball and continuous
inverse schemes. Transport through each actual rescaled basis preserves the
endpoint identities and gives uniform bounds across all maximizing bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Metric
open scoped BigOperators

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [Fintype I] [DecidableEq I]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A continuous inverse generator scheme on one common ball in each
actual rescaled logarithm chart. All constants are independent of scale,
generator exponents, and maximizing word basis. -/
theorem exists_uniform_rescaled_inverse_sections (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ (s : I → ℝ) (β : WordBasisSelections X (boundedBracketWords k)),
        IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
          (fun w => bracketWordExponent s w) β.val →
        ∀ r : ℝ, 0 ≤ r →
        let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
          (fun j => bracketWordExponent s (β.val j)) r
        ∃ (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I)
          (σ : (Fin (finrank ℝ L) → ℝ) → Fin (finrank ℝ L) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : Fin (finrank ℝ L) → ℝ) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            generatorGroupWord (fun i => Real.exp (r * s i) • X i) Exp
              (generatorSchemeWord w i (σ y)) = Exp (b.equivFun.symm y) := by
  classical
  obtain ⟨C₀, _, hc⟩ := exists_rescaledExponentialData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch
  let S := boundedBracketWords (I := I) k
  let bstd := Pi.basisFun ℝ (Fin (finrank ℝ L))
  have hf (β : WordBasisSelections X S) := exists_uniform_bounded_coordinate_inverse
    a bstd (fun j => (β.val j : FreeMagma I)) C₀ (finrank ℝ L) (by simp)
  choose ε N C hε hC hsections using hf
  obtain ⟨ε', hε', hεle⟩ := finite_positive_lower_bound Finset.univ ε (fun β _ => hε β)
  let N' := ∑ β : WordBasisSelections X S, N β
  let C' := 1 + ∑ β : WordBasisSelections X S, C β
  have hCnonneg β : 0 ≤ C β := (by norm_num : (0 : ℝ) ≤ 1).trans (hC β)
  have hC' : 1 ≤ C' := by
    dsimp [C']
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun β _ => hCnonneg β))
  refine ⟨ε', N', C', hε', hC', ?_⟩
  intro s β hβ r hr b
  have hp : rescaledLieData X S β s r ∈
      normalizedExponentialParameters a (fun j => (β.val j : FreeMagma I)) bstd C₀ := by
    have hbstd : (bstd : Fin (finrank ℝ L) → (Fin (finrank ℝ L) → ℝ)) =
        fun j => Pi.single j 1 := by
      funext j
      exact Pi.basisFun_apply ℝ _ j
    rw [hbstd]
    exact hc s β hβ r hr
  have hsec := hsections β _ hp
  obtain ⟨w, i, σ, hσ, hright⟩ := hsec
  have hsub : ball (0 : Fin (finrank ℝ L) → ℝ) ε' ⊆ ball 0 (ε β) :=
    ball_subset_ball (hεle β (Finset.mem_univ β))
  refine ⟨w, i, σ, hσ.mono hsub, ?_⟩
  intro y hy
  obtain ⟨hnorm, hlen, hamp, he⟩ := hright y (hsub hy)
  refine ⟨hnorm, hlen.trans ?_, ?_, ?_⟩
  · exact Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ β)
  · intro z hz
    have hb : C β ≤ C' := by
      have hs : C β ≤ ∑ γ : WordBasisSelections X S, C γ :=
        Finset.single_le_sum (fun γ _ => hCnonneg γ) (Finset.mem_univ β)
      dsimp [C']
      linarith
    exact (hamp z hz).trans hb
  · have hw := basis_polynomialWord b Exp hzero a hm
      (fun i => Real.exp (r * s i) • X i) (generatorSchemeWord w i (σ y))
    change Exp (b.equivFun.symm (polynomialWord (dynkinProduct a (rescaledLieData X S β s r).1)
      (rescaledLieData X S β s r).2 (generatorSchemeWord w i (σ y)))) = _ at hw
    rw [he] at hw
    exact hw.symm

end PolycyclicRecognition

end

end OAI
