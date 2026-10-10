import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierFactor
import OAI.NumberTheory.Ostmann.Characters.PolynomialWeightPair
import OAI.NumberTheory.Ostmann.Construction.TransferConjugations

namespace OAI

/-! # The concrete polynomial factors in the moving Fourier history -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

noncomputable def movingLeafIndexEquiv (n : ℕ) : TreeLeafIndex n ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (card_treeLeafIndex n)

def MovingSlotData.leafFrequencies {σ : Type*} :
    {n : ℕ} → MovingSlotData σ n → TreeLeafIndex n → ℤ
  | _, .leaf s _, _ => s
  | _, .node _ _ _ _ left _right, .inl i => left.leafFrequencies i
  | _, .node _ _ _ _ _left right, .inr i => right.leafFrequencies i

theorem movingPolynomialFourierTree_product {σ : Type*}
    (value : σ → ℕ) (ψ : ℝ → ℂ) (X z : ℝ) {n : ℕ} (T : MovingSlotData σ n)
    (L R : Polynomial ℝ) (b : Bool) :
    (∏ i : TreeLeafIndex n,
      if treeLeafTupleEquiv Bool n (transferConjugations n b) i then
        conj (normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X))
      else normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X)) =
      if b then conj (movingPolynomialFourierTree value ψ X z T L R)
      else movingPolynomialFourierTree value ψ X z T L R := by
  induction T generalizing L R b with
  | leaf s regular =>
    change (∏ _ : Unit, if b then conj _ else _) = _
    simp only [Fintype.prod_unique]
    rfl
  | @node n s CL CR u left right ihL ihR =>
    change (∏ i : TreeLeafIndex n ⊕ TreeLeafIndex n, _) = _
    rw [Fintype.prod_sum_type]
    change (∏ i : TreeLeafIndex n, if treeLeafTupleEquiv Bool n (transferConjugations n b) i
        then conj _ else _) *
      (∏ i : TreeLeafIndex n, if treeLeafTupleEquiv Bool n (transferConjugations n (!b)) i
        then conj _ else _) = _
    simp only [MovingSlotData.leafFrequencies, MovingSlotData.leafPolynomials]
    rw [ihL, ihR]
    cases b
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      change star _ * _ = star (_ * star _)
      rw [star_mul, star_star]
      exact mul_comm _ _

noncomputable def movingLeafNormalizedPolynomial {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X : ℝ) (i : TreeLeafIndex n) : Polynomial ℝ :=
  Polynomial.C X⁻¹ * T.leafPolynomials value L R i

theorem movingLeafNormalizedPolynomial_eval {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (L R : Polynomial ℝ) (X z : ℝ) (i : TreeLeafIndex n) :
    (movingLeafNormalizedPolynomial value T L R X i).eval z =
      (T.leafPolynomials value L R i).eval z / X := by
  simp only [movingLeafNormalizedPolynomial, Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv]
  ring

/-- Exactly one clipped Fourier polynomial per terminal leaf, with the
conjugation imposed by its actual left/right path. -/
noncomputable def movingFourierPolynomialFactors {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : Fin (2 ^ n) → ClippedPolynomialFactor :=
  fun j =>
    let i := (movingLeafIndexEquiv n).symm j
    let f := fourierPolynomialFactor (movingLeafNormalizedPolynomial value T L R X i)
      ψ (T.leafFrequencies i) lo hi hlo hhi
    if treeLeafTupleEquiv Bool n (transferConjugations n false) i then f.conjugate else f

theorem movingFourierPolynomialFactors_value {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (z : ℝ)
    (hrange : ∀ i, (T.leafPolynomials value L R i).eval z / X ∈ Set.Icc lo hi) :
    smoothPolynomialWeight (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) z =
      movingPolynomialFourierTree value ψ X z T L R := by
  rw [smoothPolynomialWeight]
  have he := (movingLeafIndexEquiv n).prod_comp
    (fun j => (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).value z)
  rw [← he]
  have ht (i : TreeLeafIndex n) :
      (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi
        (movingLeafIndexEquiv n i)).value z =
      if treeLeafTupleEquiv Bool n (transferConjugations n false) i then
        conj (normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X))
      else normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X) := by
    simp only [movingFourierPolynomialFactors, Equiv.symm_apply_apply]
    have hv := ClippedPolynomialFactor.value_of_mem
      (fourierPolynomialFactor (movingLeafNormalizedPolynomial value T L R X i)
        ψ (T.leafFrequencies i) lo hi hlo hhi) z
      (by simpa only [fourierPolynomialFactor, movingLeafNormalizedPolynomial_eval] using hrange i)
    have hv' : (fourierPolynomialFactor (movingLeafNormalizedPolynomial value T L R X i)
        ψ (T.leafFrequencies i) lo hi hlo hhi).value z =
        normalizedFourierProfile ψ (T.leafFrequencies i)
          ((T.leafPolynomials value L R i).eval z / X) := by
      rw [hv]
      exact congrArg (normalizedFourierProfile ψ (T.leafFrequencies i))
        (movingLeafNormalizedPolynomial_eval value T L R X z i)
    split_ifs
    · rw [ClippedPolynomialFactor.conjugate_value]
      exact congrArg conj hv'
    · exact hv'
  simp_rw [ht]
  exact movingPolynomialFourierTree_product value ψ X z T L R false

theorem movingFourierPolynomialFactors_degree {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1) (j : Fin (2 ^ n)) :
    (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j).polynomial.natDegree ≤ 2 := by
  have hp := T.leafPolynomials_degree value L R 1 hL hR ((movingLeafIndexEquiv n).symm j)
  have hn : (movingLeafNormalizedPolynomial value T L R X
      ((movingLeafIndexEquiv n).symm j)).natDegree ≤ 2 := by
    apply Polynomial.natDegree_mul_le.trans
    simpa only [Polynomial.natDegree_C, zero_add, mul_one] using hp
  dsimp only [movingFourierPolynomialFactors]
  split_ifs <;> exact hn

end Ostmann

end OAI
