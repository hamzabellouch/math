import OAI.Combinatorics.Progressions.Dynamics.NormalizedTwistUniformAmbientBudget
import OAI.Combinatorics.Progressions.Lattices.NormalizedResidueSpatialHaarBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_spatial_haar_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) [NeZero W.modulus]
      {P E Rrank : ℝ}, 0 ≤ P → 0 ≤ E →
      (Fintype.card X : ℝ) ≤ P → (Fintype.card (Σ j, J j) : ℝ) ≤ P →
      (L : ℝ) ≤ Real.exp P → (W.cover : ℝ) ≤ Real.exp P → (W.modulus : ℝ) ≤ Real.exp P →
      ∀ (N : X → ℕ),
      (∀ i, Real.exp ((max P E + A) ^ A) ≤ (N i : ℝ)) →
      Real.exp ((max P E + A) ^ A) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ integerBox N, W.eval N poly x) -
        (𝔼 r : X → ZMod W.modulus, ∫ x, W.frozenSingleSiteHaarReference U ν r x
          ∂unitBoxMeasure X)‖ ≤
        Real.exp (-E) := by
  obtain ⟨C, hC, hcomp⟩ := exists_normalizedTwist_uniform_ambient_haar_budget m
  let B : Polynomial ℕ := (Polynomial.X + 2 + Polynomial.C C) ^ C + 4 * Polynomial.X + 22
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨A, hA, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W _ P E Rrank
    hP hE hX hdim hL hcover hmod N hlarge hRrank hrank
  let z := max P E
  have hz : 0 ≤ z := hP.trans (le_max_left _ _)
  have hPE : max P (E + 2) ≤ z + 2 := by
    apply max_le
    · linarith [le_max_left P E]
    · dsimp [z]; linarith [le_max_right P E]
  have hbudget' : (z + 2 + C) ^ C + 4 * z + 22 ≤ (z + A) ^ A := by
    simpa [B, Polynomial.eval₂_pow] using hbudget z hz
  have hpow : (max P (E + 2) + C) ^ C ≤ (z + A) ^ A := by
    apply (pow_le_pow_left₀ (by positivity) (show max P (E + 2) + (C : ℝ) ≤ z + 2 + C by linarith) C).trans
    linarith
  have hmesh : 3 * P + (E + 2) + 20 ≤ (z + A) ^ A := by
    have hnonneg : 0 ≤ (z + 2 + C) ^ C := by positivity
    have hPz : P ≤ z := le_max_left _ _
    have hEz : E ≤ z := le_max_right _ _
    linarith
  have hfirst := hcomp U ν poly hp hm W hP (by linarith : 0 ≤ E + 2)
    hX hdim hL hcover hmod N
    (fun i => (Real.exp_le_exp.mpr hpow).trans (hlarge i))
    ((Real.exp_le_exp.mpr hpow).trans hRrank) hrank
  have hlast := W.integerBox_frozenSingleSiteHaarReference_riemann_budget U ν
    hP (by linarith : 0 ≤ E + 2) hX hL hmod N
    (fun i => (Real.exp_le_exp.mpr hmesh).trans (hlarge i))
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ integerBox N, W.eval N poly x)
    (𝔼 x ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
      (fun i => (x i : ZMod W.modulus)) (fun i => (x i : ℝ) / N i))
    (𝔼 r : X → ZMod W.modulus, ∫ x, W.frozenSingleSiteHaarReference U ν r x
      ∂unitBoxMeasure X)
  have he : 2 * Real.exp (-(E + 2)) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-(E + 2)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  linarith

end Erdos3.VectorPolynomial

end

end OAI
