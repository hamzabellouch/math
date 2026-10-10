import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureMass

namespace OAI

/-! # Matching box future conditionals with ambient root-orbit measures -/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_map_equiv {Y Z : Type*}
    [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (e : Y ≃ᵐ Z) (A : Set Y) :
    ((anchorNormalize ν A).restrict A).map e =
      (anchorNormalize (ν.map e) (e '' A)).restrict (e '' A) := by
  rw [anchorNormalize_map_equiv, e.measurableEmbedding.restrict_map,
    e.preimage_image]

namespace RootPrefixBox
variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] in
/-- The box expression, once unrestricted, is exactly the intrinsic
whole-future measure pushed along the actual root orbit through its sample. -/
lemma map_uncentered_future_eq_ambient
    (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (m : ℕ) (z : (UpperRootTransverse (d+1) × V) × c.Time) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := C.timeParam c hP₀ hf g
    let A := {t | ∀ k : ℕ, Q (T^[k+m] (F (z.1,t)))=Q (T^[k+m] (F z))}
    ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) A).restrict A).map
        (fun t => F (z.1,t)) =
      ((anchorNormalize (c.remainingTimeProduct hP₀ hf μ (F z))
        (c.remainingFutureAtom ell hell Q m (F z))).restrict
        (c.remainingFutureAtom ell hell Q m (F z))).map
        (fun u => rightAction (F z) (c.word u)) := by
  let F := C.timeParam c hP₀ hf g
  let E := (c.remainingRebase hP₀ hf z.2).toMeasurableEquiv
  let A := {t | ∀ k : ℕ,
    Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m] (F (z.1,t))) =
    Q ((fun x => rightAction x (diagonalOneParameter ell hell (-1)))^[k+m] (F z))}
  let W := fun u => rightAction (F z) (c.word u)
  have hW : Measurable W :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hF : (fun t => F (z.1,t)) = W ∘ E := by
    funext t
    exact C.timeParam_rebased c hP₀ hf g z.1 z.2 t
  have hM : (B.uncenteredIntrinsicProduct μ z).map E =
      c.remainingTimeProduct hP₀ hf μ (F z) := by
    rw [B.uncenteredIntrinsicProduct_eq_rebase_map μ z]
    exact E.map_map_symm
  change ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) A).restrict A).map
    (fun t => F (z.1,t)) = _
  rw [hF, ←Measure.map_map hW E.measurable,
    normalized_restriction_map_equiv, hM]
  rw [show E '' A = c.remainingFutureAtom ell hell Q m (F z) from
    rebase_image_futureFiber ell hell Q m z]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
