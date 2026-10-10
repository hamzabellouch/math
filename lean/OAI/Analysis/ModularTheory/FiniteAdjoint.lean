import OAI.Analysis.ModularTheory.NormalAdjointMap

namespace OAI

/-! Adjoint-weight symmetry on finite sums of normal-ordered elements.
The proof keeps the full GNS vectors, so all mixed terms are included. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def adjointRegularization
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) (n : ℕ) :=
  star T * modularTranslationCalculus (modularFrequencyGaussian n)

private lemma adjointRegularization_mem (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) (n : ℕ) :
    adjointRegularization T n ∈ modularCrossedProduct (volume : Measure ℝ) S :=
  mul_mem (star_mem hT) (modularTranslationCalculus_mem S _)

private lemma adjointRegularization_finite (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) (n : ℕ) :
    modularCoreSquareWeight S (adjointRegularization T n) < ⊤ :=
  modularCoreSquareWeight_mul_finite S _
    (modularTranslationCalculus_finite S _ (modularFrequencyGaussian_integrable n)) _

private def HasAdjointLimit (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) : Prop :=
  ∃ (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hfin : modularCoreSquareWeight S T < ⊤),
    Tendsto (fun n => modularWeightVector S (adjointRegularization T n)
      (adjointRegularization_mem S T hT n) (adjointRegularization_finite S T n))
      atTop (𝓝 (modularWeightAdjointMap S (modularWeightVector S T hT hfin)))

private lemma hasAdjointLimit_normal (S : StandardModularData H)
    (a : H →L[ℂ] H) (ha : a ∈ S.M) (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    HasAdjointLimit S (modularLpRepresentation volume S.D a * modularTranslationCalculus g) := by
  refine ⟨modularNormalOrdered_mem S a ha g, modularNormalOrdered_finite S a g hg, ?_⟩
  rw [modularWeightAdjointMap_normal S a ha g hg]
  exact modularNormalAdjointRegularized_vector_tendsto S a ha g hg

private lemma hasAdjointLimit_zero (S : StandardModularData H) :
    HasAdjointLimit S 0 := by
  have hfin : modularCoreSquareWeight S 0 < ⊤ := by
    rw [modularCoreSquareWeight_zero]
    exact ENNReal.zero_lt_top
  refine ⟨zero_mem _, hfin, ?_⟩
  have hz : modularWeightVector S 0 (zero_mem _) hfin = 0 :=
    (modularWeightVector_eq_zero_iff S 0 _ hfin).mpr rfl
  have hj : modularWeightAdjointMap S 0 = 0 := by
    apply norm_eq_zero.mp
    rw [modularWeightAdjointMap_norm, norm_zero]
  have hr (n : ℕ) : modularWeightVector S (adjointRegularization 0 n)
      (adjointRegularization_mem S 0 (zero_mem _) n) (adjointRegularization_finite S 0 n) = 0 :=
    (modularWeightVector_eq_zero_iff S _ _ _).mpr (by
      change star (0 : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) * _ = 0
      rw [star_zero (Lp H 2 (volume : Measure ℝ) →L[ℂ]
        Lp H 2 (volume : Measure ℝ)), zero_mul])
  simpa only [hr, hz, hj] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Lp H 2 (volume : Measure ℝ))) atTop (𝓝 0))

private lemma hasAdjointLimit_add (S : StandardModularData H)
    (T U : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : HasAdjointLimit S T) (hU : HasAdjointLimit S U) : HasAdjointLimit S (T + U) := by
  obtain ⟨hT, hTf, hTl⟩ := hT
  obtain ⟨hU, hUf, hUl⟩ := hU
  let hf := modularCoreSquareWeight_add_finite S U hUf T hTf
  refine ⟨add_mem hT hU, hf, ?_⟩
  have he (n : ℕ) : modularWeightVector S (adjointRegularization (T + U) n)
      (adjointRegularization_mem S (T + U) (add_mem hT hU) n)
      (adjointRegularization_finite S (T + U) n) =
      modularWeightVector S (adjointRegularization T n)
        (adjointRegularization_mem S T hT n) (adjointRegularization_finite S T n) +
      modularWeightVector S (adjointRegularization U n)
        (adjointRegularization_mem S U hU n) (adjointRegularization_finite S U n) := by
    have hreg : adjointRegularization (T + U) n =
        adjointRegularization T n + adjointRegularization U n := by
      change star (T + U) * _ = star T * _ + star U * _
      rw [star_add T U, add_mul]
    have hv := modularWeightVector_add S (adjointRegularization U n)
      (adjointRegularization_mem S U hU n) (adjointRegularization_finite S U n)
      (adjointRegularization T n) (adjointRegularization_mem S T hT n)
      (adjointRegularization_finite S T n)
    have hc : modularWeightVector S (adjointRegularization (T + U) n)
        (adjointRegularization_mem S (T + U) (add_mem hT hU) n)
        (adjointRegularization_finite S (T + U) n) =
        modularWeightVector S (adjointRegularization T n + adjointRegularization U n)
          (add_mem (adjointRegularization_mem S T hT n) (adjointRegularization_mem S U hU n))
          (modularCoreSquareWeight_add_finite S (adjointRegularization U n)
            (adjointRegularization_finite S U n) (adjointRegularization T n)
            (adjointRegularization_finite S T n)) := by
      congr 1
    exact hc.trans hv
  have ht := (hTl.add hUl).congr' (Eventually.of_forall (fun n => (he n).symm))
  rw [modularWeightVector_add S U hU hUf T hT hTf, modularWeightAdjointMap_add]
  exact ht

private lemma weight_symmetry_of_hasAdjointLimit (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (h : HasAdjointLimit S T) : modularCoreSquareWeight S (star T) = modularCoreSquareWeight S T := by
  obtain ⟨hT, hfin, hlim⟩ := h
  let ζ := modularWeightAdjointMap S (modularWeightVector S T hT hfin)
  have hz : ‖ζ‖ ^ 2 = (modularCoreSquareWeight S T).toReal := by
    rw [modularWeightAdjointMap_norm, modularWeightVector_norm_sq]
  have hs (f : Lp H 2 (volume : Measure ℝ)) :
      Tendsto (fun n => adjointRegularization T n f) atTop (𝓝 ((star T) f)) :=
    (star T).continuous.continuousAt.tendsto.comp (modularFrequencyGaussian_strong f)
  have hle := modularCoreSquareWeight_le_of_strong_weightVectors S (adjointRegularization T)
    (adjointRegularization_mem S T hT) (adjointRegularization_finite S T) (star T) hs ζ hlim
  rw [hz, ENNReal.ofReal_toReal hfin.ne] at hle
  apply le_antisymm hle
  have hn := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hlim.norm).pow 2)
  change Tendsto _ atTop (𝓝 (ENNReal.ofReal (‖ζ‖ ^ 2))) at hn
  rw [hz, ENNReal.ofReal_toReal hfin.ne] at hn
  apply le_of_tendsto hn
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  rw [modularWeightVector_norm_sq, ENNReal.ofReal_toReal (adjointRegularization_finite S T n).ne]
  exact modularCoreSquareWeight_rightMultiplier S (star T) (star_mem hT)
    (modularFrequencyGaussian n)
    ((BoundedContinuousFunction.norm_le zero_le_one).mpr (modularFrequencyGaussian_norm n))

theorem modularFiniteNormalOrdered_adjoint_weight (S : StandardModularData H)
    {I : Type*} (s : Finset I) (a : I → H →L[ℂ] H) (g : I → BoundedContinuousFunction ℝ ℂ)
    (ha : ∀ i ∈ s, a i ∈ S.M)
    (hg : ∀ i ∈ s, Integrable (fun ω : ℝ => ‖g i ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularCoreSquareWeight S
        (star (∑ i ∈ s, modularLpRepresentation volume S.D (a i) * modularTranslationCalculus (g i))) =
      modularCoreSquareWeight S
        (∑ i ∈ s, modularLpRepresentation volume S.D (a i) * modularTranslationCalculus (g i)) := by
  apply weight_symmetry_of_hasAdjointLimit
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using hasAdjointLimit_zero S
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact hasAdjointLimit_add S _ _
        (hasAdjointLimit_normal S (a i) (ha i (Finset.mem_insert_self i s)) (g i)
          (hg i (Finset.mem_insert_self i s)))
        (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

end WeakPureInfiniteness

end

end OAI
