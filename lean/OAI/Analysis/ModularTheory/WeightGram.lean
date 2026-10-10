import OAI.Analysis.ModularTheory.CoreSquareWeight
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

/-! Orthogonality of increments of the actual modular cutoff vectors after
applying a core operator. This is the Hilbert-space estimate for constructing
the finite-weight GNS vector, without a traciality assumption. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

lemma modularFourierCompression_inner
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ f (modularFourierCompression S T g) =
      inner ℂ (modularFourierInclusion S f) (T (modularFourierInclusion S g)) := by
  change inner ℂ f ((modularFourierInclusion S).toContinuousLinearMap.adjoint
      (T (modularFourierInclusion S g))) = _
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

lemma modularFourierCompression_square_inner
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ (T (modularFourierInclusion S f)) (T (modularFourierInclusion S g)) =
      inner ℂ f (modularFourierCompression S (star T * T) g) := by
  rw [modularFourierCompression_inner]
  change inner ℂ (T (modularFourierInclusion S f)) (T (modularFourierInclusion S g)) =
    inner ℂ (modularFourierInclusion S f) (T.adjoint (T (modularFourierInclusion S g)))
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

lemma modularCoreWeightVector_gram
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (n m : ℕ) (hnm : n ≤ m) :
    inner ℂ (T (modularCoreWeightVector S n)) (T (modularCoreWeightVector S m)) =
      (‖T (modularCoreWeightVector S n)‖ ^ 2 : ℝ) := by
  let X := modularFourierCompression S (star T * T)
  let P := scalarIntervalProjection n
  have hc : Commute X P := scalarLp_commute_intervalProjection X
    (modularFourierCompression_commutes S _ (mul_mem (star_mem hT) hT)) n
  have hP : P.adjoint = P := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (scalarIntervalProjection_isStarProjection n).isSelfAdjoint.star_eq
  have hn : P (modularWeightCutoffVector n) = modularWeightCutoffVector n :=
    modularWeightCutoffVector_project n n le_rfl
  have hm : P (modularWeightCutoffVector m) = modularWeightCutoffVector n :=
    modularWeightCutoffVector_project n m hnm
  have he : X (P (modularWeightCutoffVector m)) = P (X (modularWeightCutoffVector m)) :=
    congrArg (fun F : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) =>
      F (modularWeightCutoffVector m)) hc.eq
  change inner ℂ (T (modularFourierInclusion S (modularWeightCutoffVector n)))
    (T (modularFourierInclusion S (modularWeightCutoffVector m))) = _
  rw [modularFourierCompression_square_inner]
  change inner ℂ (modularWeightCutoffVector n) (X (modularWeightCutoffVector m)) = _
  calc
    _ = inner ℂ (P (modularWeightCutoffVector n)) (X (modularWeightCutoffVector m)) := by rw [hn]
    _ = inner ℂ (modularWeightCutoffVector n) (P (X (modularWeightCutoffVector m))) := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hP]
    _ = inner ℂ (modularWeightCutoffVector n) (X (modularWeightCutoffVector n)) := by
      rw [← he, hm]
    _ = inner ℂ (T (modularCoreWeightVector S n)) (T (modularCoreWeightVector S n)) :=
      (modularFourierCompression_square_inner S T _ _).symm
    _ = _ := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

lemma modularCoreWeightVector_difference_sq
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (n m : ℕ) (hnm : n ≤ m) :
    ‖T (modularCoreWeightVector S n) - T (modularCoreWeightVector S m)‖ ^ 2 =
      ‖T (modularCoreWeightVector S m)‖ ^ 2 - ‖T (modularCoreWeightVector S n)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), modularCoreWeightVector_gram S T hT n m hnm]
  change ‖T (modularCoreWeightVector S n)‖ ^ 2 -
    2 * ‖T (modularCoreWeightVector S n)‖ ^ 2 +
    ‖T (modularCoreWeightVector S m)‖ ^ 2 = _
  ring

lemma modularCoreWeightVector_norm_sq_le
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : modularCoreSquareWeight S T < ⊤) (n : ℕ) :
    ‖T (modularCoreWeightVector S n)‖ ^ 2 ≤ (modularCoreSquareWeight S T).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hT.ne).mp
  exact le_iSup (fun n => ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2)) n

lemma modularCoreWeightVector_norm_sq_tendsto
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hfin : modularCoreSquareWeight S T < ⊤) :
    Tendsto (fun n => ‖T (modularCoreWeightVector S n)‖ ^ 2) atTop
      (𝓝 (modularCoreSquareWeight S T).toReal) := by
  have hm : Monotone (fun n => ‖T (modularCoreWeightVector S n)‖ ^ 2) := by
    intro n m hnm
    have h := modularCoreCutoffFunctional_mono S n m hnm (star T * T)
      (mul_mem (star_mem hT) hT) (star_mul_self_nonneg T)
    rw [modularCoreCutoffFunctional_square, modularCoreCutoffFunctional_square] at h
    exact Complex.real_le_real.mp h
  have hb : BddAbove (Set.range (fun n => ‖T (modularCoreWeightVector S n)‖ ^ 2)) := by
    refine ⟨(modularCoreSquareWeight S T).toReal, ?_⟩
    rintro x ⟨n, rfl⟩
    exact modularCoreWeightVector_norm_sq_le S T hfin n
  have he : (modularCoreSquareWeight S T).toReal =
      ⨆ n, ‖T (modularCoreWeightVector S n)‖ ^ 2 := by
    unfold modularCoreSquareWeight
    rw [ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [he]
  exact tendsto_atTop_ciSup hm hb

lemma modularCoreWeightVector_cauchy
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hfin : modularCoreSquareWeight S T < ⊤) :
    CauchySeq (fun n => T (modularCoreWeightVector S n)) := by
  let a (n : ℕ) := ‖T (modularCoreWeightVector S n)‖ ^ 2
  let L := (modularCoreSquareWeight S T).toReal
  have ht := modularCoreWeightVector_norm_sq_tendsto S T hT hfin
  refine Metric.cauchySeq_iff.mpr ?_
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε ^ 2) (sq_pos_of_pos hε)
  have hd (n m : ℕ) (hn : N ≤ n) (hnm : n ≤ m) :
      ‖T (modularCoreWeightVector S n) - T (modularCoreWeightVector S m)‖ < ε := by
    have hn' : |a n - L| < ε ^ 2 := by
      simpa only [Real.dist_eq] using hN n hn
    have hm' : a m ≤ L := modularCoreWeightVector_norm_sq_le S T hfin m
    have hsq := modularCoreWeightVector_difference_sq S T hT n m hnm
    have hlo := (abs_lt.mp hn').1
    dsimp only [a, L] at hlo hm'
    nlinarith [norm_nonneg (T (modularCoreWeightVector S n) - T (modularCoreWeightVector S m))]
  refine ⟨N, fun n hn m hm => ?_⟩
  rcases le_total n m with hnm | hmn
  · simpa only [dist_eq_norm] using hd n m hn hnm
  · simpa only [dist_eq_norm, norm_sub_rev] using hd m n hm hmn

theorem exists_modularCoreWeightVector_limit
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hfin : modularCoreSquareWeight S T < ⊤) :
    ∃ ξ : Lp H 2 (volume : Measure ℝ),
      Tendsto (fun n => T (modularCoreWeightVector S n)) atTop (𝓝 ξ) :=
  cauchySeq_tendsto_of_complete (modularCoreWeightVector_cauchy S T hT hfin)

end WeakPureInfiniteness

end

end OAI
