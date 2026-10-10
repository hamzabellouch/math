import OAI.Analysis.FreeEntropy.HeatTensor

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem wordEval_append {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ} (X : Fin n → H →L[ℂ] H) (u v : List (Fin n)) :
    wordEval X (u ++ v) = wordEval X u * wordEval X v := by
  simp [wordEval]

 theorem star_wordEval {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (w : List (Fin n)) :
    star (wordEval X w) = wordEval X w.reverse := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    simp only [wordEval, List.map_cons, List.prod_cons, star_mul, (hX i).star_eq,
      List.reverse_cons, List.map_append, List.prod_append, ] at *
    rw [ih]
    simp

 theorem inner_wordVector {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (u v : List (Fin n)) :
    inner ℂ (wordEval X u τ.vacuum) (wordEval X v τ.vacuum) =
      wordMoment τ X (u.reverse ++ v) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    star_wordEval X hX u]
  simp only [wordMoment, trace, wordEval_append, mul_apply_eq_comp]

theorem polynomialVector_norm_sq_eq_of_moments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hY : ∀ i, IsSelfAdjoint (Y i))
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w) (p : WordPolynomial n) :
    ‖polynomialVector τ X p‖ ^ 2 = ‖polynomialVector ρ Y p‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  simp only [polynomialVector, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_wordVector τ X hX,
    inner_wordVector ρ Y hY, hm]

 theorem derivativeMoment_eq_of_moments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w) (i : Fin n) (w : List (Fin n)) :
    derivativeMoment τ X i w = derivativeMoment ρ Y i w := by
  simp only [derivativeMoment, hm]

theorem freeFisher_eq_of_wordMoments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hY : ∀ i, IsSelfAdjoint (Y i))
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w)
    (heX : ∃ ξ, ConjugateSystem τ X ξ) (heY : ∃ ξ, ConjugateSystem ρ Y ξ) :
    freeFisher τ X = freeFisher ρ Y := by
  obtain ⟨ξ,hξ⟩ := heX
  obtain ⟨η,hη⟩ := heY
  rw [freeFisher_variational τ X hξ, freeFisher_variational ρ Y hη]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg iSup
  funext p
  apply congrArg ENNReal.ofReal
  unfold fisherTest
  rw [polynomialVector_norm_sq_eq_of_moments τ ρ X Y hX hY hm]
  congr 2
  simp only [polynomialDerivative, Finsupp.linearCombination_apply, Finsupp.sum,
    derivativeMoment_eq_of_moments τ ρ X Y hm]

 theorem continuous_heatTuple {n : ℕ} (X S : Fin n → H →L[ℂ] H) (i : Fin n) :
    Continuous (fun u : ℝ => heatTuple X S u i) := by
  unfold heatTuple
  fun_prop

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem heat_conjugates_exist {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    ∃ ξ, ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u) ξ :=
  exists_conjugate_of_fisher_le _ _ (n/u) (heat_freeFisher_le J X hX σ hσ hs u hu)

 theorem heat_freeFisher_measurable {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    Measurable (fun u : Set.Ioi (0 : ℝ) => freeFisher (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u.val)) := by
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_freeFisher (tracialVector B N G)
  · intro i
    exact (continuous_heatTuple X (fun i => semicircularN (σ i)) i).comp continuous_subtype_val
  · intro u
    exact heat_conjugates_exist J X hX σ hσ hs u.val u.property

end FreeTensor
end FiniteEntropySeparation

end

end OAI
