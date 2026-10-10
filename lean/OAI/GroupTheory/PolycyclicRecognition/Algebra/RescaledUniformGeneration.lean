import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformCoordinateGeneration

namespace OAI

/-! # Uniform generator words in the actual rescaled Lie model

The compact-family theorem is transported back through the actual coordinate
bases. Finiteness of the word-basis choices gives bounds independent of the
maximizing basis, scale, and generator exponents.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators

variable {I L G : Type*} [LieRing L] [LieAlgebra ℝ L] [Group G]

/-- Direct polynomial evaluation transports to the actual group word. -/
theorem basis_polynomialWord {n c : ℕ} (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hzero : Exp 0 = 1) (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (X : I → L) (w : List (I × ℝ)) :
    Exp (b.equivFun.symm (polynomialWord (dynkinProduct a (basisBracket b))
      (fun i => b.equivFun (X i)) w)) = generatorGroupWord X Exp w := by
  have hp (x y : Fin n → ℝ) :
      Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
        Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm]
  induction w with
  | nil => simp only [polynomialWord, map_zero, generatorGroupWord_nil, hzero]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    rw [polynomialWord, hp, ih, map_smul, LinearEquiv.symm_apply_apply,
      generatorGroupWord_cons]

variable [FiniteDimensional ℝ L] [Fintype I] [DecidableEq I]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual rescaled boxes have generator-word bounds uniform over all
exponents, nonnegative scales, and maximizing word bases. -/
theorem exists_uniform_rescaled_generator_words (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords k)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ R →
      ∃ u : List (I × ℝ), u.length ≤ N ∧ (∀ z ∈ u, |z.2| ≤ C) ∧
        generatorGroupWord (fun i => Real.exp (r * s i) • X i) Exp u = Exp v := by
  classical
  obtain ⟨C₀, _, hc⟩ := exists_rescaledExponentialData_bound X hk hletters b₀
    Exp hinj hzero hneg hadd a hm j ρ hρ hmatch
  let S := boundedBracketWords (I := I) k
  let bstd := Pi.basisFun ℝ (Fin (finrank ℝ L))
  have hf (β : WordBasisSelections X S) := exists_uniform_bounded_coordinate_words
    a bstd (fun j => (β.val j : FreeMagma I)) C₀ R
  choose N C hC hword using hf
  let N' := ∑ β : WordBasisSelections X S, N β
  let C' := 1 + ∑ β : WordBasisSelections X S, C β
  have hCnonneg β : 0 ≤ C β := (by norm_num : (0 : ℝ) ≤ 1).trans (hC β)
  have hC' : 1 ≤ C' := by
    dsimp [C']
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun β _ => hCnonneg β))
  refine ⟨N', C', hC', ?_⟩
  intro s β hβ r hr v hv
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun j => bracketWordExponent s (β.val j)) r
  have hp : rescaledLieData X S β s r ∈
      normalizedExponentialParameters a (fun j => (β.val j : FreeMagma I)) bstd C₀ := by
    have hbstd : (bstd : Fin (finrank ℝ L) → (Fin (finrank ℝ L) → ℝ)) =
        fun j => Pi.single j 1 := by
      funext j
      exact Pi.basisFun_apply ℝ _ j
    rw [hbstd]
    exact hc s β hβ r hr
  obtain ⟨u, hu, hCu, he⟩ := hword β _ hp (b.equivFun v) hv
  refine ⟨u, hu.trans ?_, ?_, ?_⟩
  · exact Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ β)
  · intro z hz
    have hb : C β ≤ C' := by
      have hs : C β ≤ ∑ γ : WordBasisSelections X S, C γ :=
        Finset.single_le_sum (fun γ _ => hCnonneg γ) (Finset.mem_univ β)
      dsimp [C']
      linarith
    exact (hCu z hz).trans hb
  · have hw := basis_polynomialWord b Exp hzero a hm
      (fun i => Real.exp (r * s i) • X i) u
    change Exp (b.equivFun.symm (polynomialWord (dynkinProduct a (rescaledLieData X S β s r).1)
      (rescaledLieData X S β s r).2 u)) = _ at hw
    rw [he, LinearEquiv.symm_apply_apply] at hw
    exact hw.symm

end PolycyclicRecognition

end

end OAI
