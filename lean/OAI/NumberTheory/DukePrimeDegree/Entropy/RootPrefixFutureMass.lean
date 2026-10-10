import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixCountableInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureShift

namespace OAI

/-! # Rebasing the actual intrinsic masses in a root box -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma uncenteredIntrinsicProduct_eq_rebase_map
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    B.uncenteredIntrinsicProduct μ z =
      (c.remainingTimeProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map
        (c.remainingRebase hP₀ hf z.2).symm := by
  let W := c.remainingWordHomeomorph hP₀ hf
  let E := c.remainingRebase hP₀ hf z.2
  change ((c.remainingIntrinsicProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map
    (Homeomorph.mulLeft (W z.2))).map W.symm =
    ((c.remainingIntrinsicProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)).map W.symm).map E.symm
  rw [Measure.map_map W.symm.measurable (Homeomorph.mulLeft (W z.2)).measurable,
    Measure.map_map E.symm.measurable W.symm.measurable]
  congr 1
  funext v
  apply E.injective
  rw [Function.comp_apply, Function.comp_apply, E.apply_symm_apply]
  apply W.injective
  rw [c.remainingRebase_word hP₀ hf, W.apply_symm_apply, W.apply_symm_apply]
  exact inv_mul_cancel_left (W z.2) v

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma uncenteredIntrinsicProduct_apply
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × V) × c.Time)
    (A : Set c.Time) (hA : MeasurableSet A) :
    B.uncenteredIntrinsicProduct μ z A =
      c.remainingTimeProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)
        ((c.remainingRebase hP₀ hf z.2) '' A) := by
  rw [B.uncenteredIntrinsicProduct_eq_rebase_map μ z,
    Measure.map_apply (c.remainingRebase hP₀ hf z.2).symm.measurable hA]
  congr 1
  exact ((c.remainingRebase hP₀ hf z.2).toEquiv.image_eq_preimage_symm A).symm

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
lemma rebase_image_futureFiber
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (m : ℕ) (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    (c.remainingRebase hP₀ hf z.2) ''
      {t | ∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g (z.1,t))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g z))} =
      c.remainingFutureAtom ell hell Q m (C.timeParam c hP₀ hf g z) := by
  let E := c.remainingRebase hP₀ hf z.2
  ext u
  constructor
  · rintro ⟨t,ht,rfl⟩ k
    rw [← C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
    exact ht k
  · intro hu
    refine ⟨E.symm u, ?_, E.apply_symm_apply u⟩
    intro k
    rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 (E.symm u)]
    change Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
      (rightAction (C.timeParam c hP₀ hf g z) (c.word (E (E.symm u))))) = _
    rw [E.apply_symm_apply]
    exact hu k

/-- A box containing its whole future fiber computes the unrestricted
intrinsic future mass exactly after rebasing at the sampled point. -/
lemma uncenteredIntrinsicProduct_wholeFuture
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q) (m : ℕ)
    (z : (UpperRootTransverse (d+1) × V) × c.Time)
    (hcontained : {t | ∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g (z.1,t))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g z))} ⊆ B.time) :
    B.uncenteredIntrinsicProduct μ z
      ({t | ∀ k : ℕ,
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g (z.1,t))) =
        Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m]
          (C.timeParam c hP₀ hf g z))} ∩ B.time) =
      c.remainingTimeProduct hP₀ hf μ (C.timeParam c hP₀ hf g z)
        (c.remainingFutureAtom ell hell Q m (C.timeParam c hP₀ hf g z)) := by
  rw [Set.inter_eq_left.mpr hcontained, B.uncenteredIntrinsicProduct_apply μ z]
  · rw [rebase_image_futureFiber ell hell Q m z]
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_eq_fun
      (hQ.comp (((continuous_rightAction _).measurable.iterate (k+m)).comp
        ((C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable.comp
          measurable_prodMk_left))) measurable_const

/-- Once a box contains the entire future fiber, its conditional present
information is exactly the ratio of the two intrinsic future masses. -/
theorem conditionalInformation_eq_wholeFuture_ratio
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k]
        (rightAction x ((completeRootChain (d+1)).word v))) =
      Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k] x))
    (hcontained : ∀ᵐ z ∂B.coordinateMeasure μ,
      countableFutureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
        Q (C.timeParam c hP₀ hf g) z ⊆ B.time) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP₀ hf g
    conditionalInformation (B.coordinateMeasure μ) (Q ∘ F)
      (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z)))
      =ᵐ[B.coordinateMeasure μ] fun z => -Real.log
        ((c.remainingTimeProduct hP₀ hf μ (F z)).real
            (c.remainingFutureAtom ell hell Q 0 (F z)) /
          (c.remainingTimeProduct hP₀ hf μ (F z)).real
            (c.remainingFutureAtom ell hell Q 1 (F z))) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := C.timeParam c hP₀ hf g
  have hT : Measurable T := (continuous_rightAction _).measurable
  filter_upwards [B.conditionalInformation_countableFuture_uncenteredIntrinsicProduct
    R hBR μ hQ hT hgood, hcontained] with z hz hc
  refine hz.trans (congrArg (-Real.log ·) ?_)
  have hp : {t | Q (F (z.1,t))=Q (F z)} ∩ countableFutureFiber T Q F z =
      {t | ∀ k : ℕ, Q (T^[k+0] (F (z.1,t)))=Q (T^[k+0] (F z))} := by
    ext t
    constructor
    · rintro ⟨hzero,hfuture⟩ k
      cases k with
      | zero => simpa using hzero
      | succ k => exact hfuture k
    · intro ht
      exact ⟨by simpa using ht 0, fun k => ht (k+1)⟩
  have hfut : countableFutureFiber T Q F z =
      {t | ∀ k : ℕ, Q (T^[k+1] (F (z.1,t)))=Q (T^[k+1] (F z))} := rfl
  have hc0 : {t | ∀ k : ℕ, Q (T^[k+0] (F (z.1,t)))=Q (T^[k+0] (F z))} ⊆ B.time := by
    rw [←hp]
    exact Set.inter_subset_right.trans hc
  change (B.uncenteredIntrinsicProduct μ z).real
      (({t | Q (F (z.1,t))=Q (F z)} ∩ countableFutureFiber T Q F z) ∩ B.time) /
      (B.uncenteredIntrinsicProduct μ z).real (countableFutureFiber T Q F z ∩ B.time) = _
  rw [hp,hfut]
  exact congrArg₂ (fun a b : ℝ≥0∞ => a.toReal / b.toReal)
    (B.uncenteredIntrinsicProduct_wholeFuture μ ell hell Q hQ 0 z hc0)
    (B.uncenteredIntrinsicProduct_wholeFuture μ ell hell Q hQ 1 z hc)

end RootPrefixBox
end DukePrimeDegree

end

end OAI
