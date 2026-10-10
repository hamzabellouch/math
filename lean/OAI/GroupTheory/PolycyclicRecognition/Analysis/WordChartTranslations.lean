import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformDynkinDifference
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # Small left translations in the actual nilpotent word chart -/

noncomputable section
namespace PolycyclicRecognition
open Module LieModule
open scoped Manifold

variable {L I E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [T2Space G] in
/-- The coordinate displacement of left multiplication by `exp (-h)`
is at most a common constant times the normalized coordinate size of `h`.
The constant works for every scale. -/
theorem exists_uniform_word_chart_translation_bound
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (hinj : Function.Injective Exp)
    (X : I → L) {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (β : WordBasisSelections X (boundedBracketWords d))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (e (finiteDynkinPolynomial a ![x, y])) = Exp (e x) * Exp (e y))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r → ∀ h : L,
      let br := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
        (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
      ‖br.equivFun h‖ ≤ 1 → ∀ z : Fin (finrank ℝ L) → ℝ, ‖z‖ ≤ R →
      ‖br.equivFun (finiteDynkinPolynomial a ![-h, br.equivFun.symm z]) - z‖ ≤
        C * ‖br.equivFun h‖ := by
  obtain ⟨K, hK, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound X hd b₀
  obtain ⟨A, hA, hdiff⟩ :=
    exists_uniform_finiteDynkinPolynomial_difference_bound (L := L)
      (J := Fin (finrank ℝ L)) a hK
  let M := max R 1
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_right _ _)
  have hzero (v : L) : finiteDynkinPolynomial a ![0, v] = v := by
    have hv : Exp (e (finiteDynkinPolynomial a ![0, v])) = Exp (e v) := by
      simpa only [map_zero, hExp.map_zero, one_mul] using hm 0 v
    exact e.toLinearEquiv.injective (hinj hv)
  refine ⟨A * (1 + M) ^ c, mul_nonneg hA (pow_nonneg (by linarith) _), ?_⟩
  intro r hr h
  dsimp only
  let br := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
  intro hh z hz
  have hv : ‖br.equivFun (br.equivFun.symm z)‖ ≤ M := by
    simpa only [LinearEquiv.apply_symm_apply] using hz.trans (le_max_left R 1)
  have hhM : ‖br.equivFun h‖ ≤ M := hh.trans (le_max_right R 1)
  have hh' : ‖br.equivFun (-h)‖ ≤ M := by simpa only [map_neg, norm_neg] using hhM
  have hb := hdiff br (hbracket (fun _ : I => 1) β hβ (Real.log r) (Real.log_nonneg hr))
    ![-h, br.equivFun.symm z] ![0, br.equivFun.symm z] M ‖br.equivFun h‖ hM
    (norm_nonneg _)
    (by intro i; fin_cases i; exact hh'; exact hv)
    (by intro i; fin_cases i; simpa using hM; exact hv)
    (by intro i; fin_cases i <;> simp)
  simpa only [hzero, map_sub, LinearEquiv.apply_symm_apply, mul_assoc] using hb

end PolycyclicRecognition

end

end OAI
