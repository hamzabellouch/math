import Mathlib
import OAI.Analysis.AffineBernstein.Basic
import OAI.Analysis.AffineBernstein.TubeFrame

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma tubeTangent_linearIndependent (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) : LinearIndependent ℝ (tubeTangent bS bE) := by
  let j : ι ⊕ κ → ι ⊕ (κ ⊕ Unit) := Sum.map id Sum.inl
  have hj : Function.Injective j := Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩
  have hh := (bS.prod bE.toBasis).linearIndependent.comp j hj
  have heq : tubeTangent bS bE = (bS.prod bE.toBasis) ∘ j := by
    funext i
    cases i <;> simp [tubeTangent,j]
  rw [heq]
  exact hh

omit [DecidableEq ι] [DecidableEq κ] in
lemma tube_dimension_equiv {n : ℕ}
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (L : (S × E) ≃L[ℝ] (Space n × ℝ)) : Nonempty (Fin n ≃ ι ⊕ κ) := by
  let : FiniteDimensional ℝ S := Module.Finite.of_basis bS
  let : FiniteDimensional ℝ E := Module.Finite.of_basis bE.toBasis
  have hdim := L.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_eq_card_basis bS,
    Module.finrank_eq_card_basis bE.toBasis] at hdim
  simp only [Fintype.card_sum,Fintype.card_unit,Module.finrank_self,
    finrank_euclideanSpace,Fintype.card_fin] at hdim
  apply Fintype.card_eq.mp
  simp only [Fintype.card_fin,Fintype.card_sum]
  omega

/- An actual flat-normal coordinate injection with a continuous linear left
inverse. These chart data are produced from the frames, not postulated. -/
omit [DecidableEq ι] in
lemma exists_flat_tube_chart {n : ℕ} (bS : Module.Basis ι ℝ S)
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (e : Fin n ≃ ι ⊕ κ) :
    ∃ (J : Space n →L[ℝ] S × E) (C : S × E →L[ℝ] Space n),
      Function.Injective J ∧ (∀ x, C (J x) = x) ∧
      (∀ x, inner ℝ (J x).2 (bE (Sum.inr ())) = 0) ∧
      (∀ i, J (coordinateVector n i) = tubeTangent bS bE (e i)) := by
  let : FiniteDimensional ℝ S := Module.Finite.of_basis bS
  let : FiniteDimensional ℝ E := Module.Finite.of_basis bE.toBasis
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb (i : Fin n) : b i = coordinateVector n i := by
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ i
  let j := b.constr ℝ (tubeTangent bS bE ∘ e)
  have hj : Function.Injective j := b.injective_constr_of_linearIndependent
    ((tubeTangent_linearIndependent bS bE).comp e e.injective)
  obtain ⟨c,hc⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let J := j.toContinuousLinearMap
  let C := c.toContinuousLinearMap
  have hJ (i : Fin n) : J (coordinateVector n i) = tubeTangent bS bE (e i) := by
    change j (coordinateVector n i) = _
    rw [← hb]
    exact b.constr_basis ℝ _ i
  refine ⟨J,C,hj,?_,?_,hJ⟩
  · intro x
    exact congrArg (fun l : Space n →ₗ[ℝ] Space n => l x) hc
  · have ht : ((InnerProductSpace.toDual ℝ E (bE (Sum.inr ()))).comp
        ((ContinuousLinearMap.snd ℝ S E).comp J)).toLinearMap = 0 := by
      apply b.ext
      intro i
      change inner ℝ (bE (Sum.inr ())) (J (b i)).2 = 0
      rw [hb i,hJ]
      cases h : e i with
      | inl k => simp [tubeTangent]
      | inr k => simp [tubeTangent,bE.inner_eq_ite]
    intro x
    have hh := congrArg (fun l : Space n →ₗ[ℝ] ℝ => l x) ht
    simpa [real_inner_comm] using hh

end AffineBernstein
end

end OAI
