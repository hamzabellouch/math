import OAI.Probability.InvariantIsing.Magnetic.RestrictedBlockOverlap
import OAI.Probability.InvariantIsing.Fields.VectorTransitionZero

namespace OAI

/-! Zero Gaussian increments repeat the same conditional overlap level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators

namespace InvariantIsing

lemma restrictedPairCoordinateMean_tied {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ j < n, 0 < b j) (i : Fin n) (hv : v i = 0) (j : Fin N) (z : Fin N → ℝ) :
    restrictedPairCoordinateMean hN S hS n b v hb i.castSucc j z =
      restrictedPairCoordinateMean hN S hS n b v hb i.succ j z := by
  induction n generalizing b v z with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let bs := fun k => b (k + 1)
    let vs := fun k => v (k + 1)
    have hbs : ∀ k < n, 0 < bs k := fun k hk => hb (k + 1) (by omega)
    revert hv
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hv
      rw [Fin.castSucc_zero, restrictedPairCoordinateMean_zero,
        restrictedCoordinateMean_succ, restrictedPairCoordinateMean_succ]
      have hF := restrictedFieldRecursion_regular hN S hS n bs vs hbs
      change v 0 = 0 at hv
      rw [hv, vectorGaussianTransition_zero hN (b 0) _ hF.1 hF.2 z]
      simp only [integral_dirac, restrictedPairCoordinateMean_zero]
    · intro hv
      change restrictedPairCoordinateMean hN S hS (n + 1) b v hb k.castSucc.succ j z =
        restrictedPairCoordinateMean hN S hS (n + 1) b v hb k.succ.succ j z
      rw [restrictedPairCoordinateMean_succ, restrictedPairCoordinateMean_succ]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => ih bs vs hbs k hv y)

lemma fieldStepVariance_tied (h : FieldStep) (i : Fin h.depth)
    (hi : h.height i.castSucc = h.height i.succ) : fieldStepVariance h i = 0 := by
  rw [fieldStepVariance, dite_eq_left i.isLt]
  have hg : (scalarFieldIncrements h).get
      ⟨i.val, by simpa only [scalarFieldIncrements_length] using i.isLt⟩ =
      ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
    exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
      NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) _
  rw [hg]
  apply Subtype.ext
  change (fieldIncrement h i.succ).2 = 0
  simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel]
  change h.height i.succ - h.height i.castSucc = 0
  exact sub_eq_zero.mpr hi.symm

lemma restrictedBlockPairMean_tied {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ)
    (i : Fin h.depth) (hi : h.height i.castSucc = h.height i.succ) :
    restrictedBlockPairMean hN S hS h b i.castSucc =
      restrictedBlockPairMean hN S hS h b i.succ := by
  rw [restrictedBlockPairMean_eq_average, restrictedBlockPairMean_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => restrictedPairCoordinateMean_tied hN S hS _ _ _ _ i
    (fieldStepVariance_tied h i hi) j z)

end InvariantIsing

end

end OAI
