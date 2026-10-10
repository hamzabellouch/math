import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteRealProductKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureShift
import Mathlib.Probability.Kernel.MeasurableLIntegral

namespace OAI

/-! # A measurable version of the actual remaining-root product

This supplies measurability of the mass of a whole future atom, rather
than imposing measurability as an additional dynamical hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

/-- The intrinsic product has an s-finite kernel version. -/
theorem exists_remainingTimeKernel (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ κ : Kernel (X (d+1)) c.Time, IsSFiniteKernel κ ∧
      ∀ᵐ x ∂μ, κ x = c.remainingTimeProduct hP hf μ x := by
  let I := ↥(allPositiveRoots (d+1) \ P)
  let hij (p : I) := ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2
  have hfree (p : I) : ∀ᵐ x ∂μ, ∀ v : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection (hij p) v) = x → v = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _
  let κ (p : I) := intrinsicRootKernel (hij p) μ (hfree p)
  obtain ⟨η, hη, heq⟩ := exists_realProductKernel κ
  let := hη
  let E := c.remainingEuclideanCoordinates hf
  refine ⟨η.map E.symm, inferInstance, ?_⟩
  have hleaf := ae_all_iff.mpr (fun p : I => ae_intrinsicRootKernel_eq (hij p) μ (hfree p))
  filter_upwards [hleaf] with x hx
  rw [Kernel.map_apply _ E.symm.measurable, heq, c.remainingTimeProduct_eq_map hP hf μ x]
  congr 2
  funext p
  exact hx p

lemma measurableSet_remainingFutureRelation {n : ℕ}
    {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hf : c.finalEntries = allPositiveRoots n)
    (ell : Fin n → ℝ) (hell : ∑ k, ell k = 0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) :
    MeasurableSet {z : X n × c.Time | z.2 ∈ c.remainingFutureAtom ell hell Q m z.1} := by
  let T : X n → X n := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable (fun z : X n × c.Time => rightAction z.1 (c.word z.2)) :=
    (continuous_rightAction_uncurry n).measurable.comp
      (measurable_fst.prodMk ((c.word_isEmbedding_remaining hf).continuous.measurable.comp
        measurable_snd))
  change MeasurableSet {z : X n × c.Time |
    ∀ k : ℕ, Q (T^[k+m] (rightAction z.1 (c.word z.2))) = Q (T^[k+m] z.1)}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_eq_fun (hQ.comp ((hT.iterate (k+m)).comp hF))
    (hQ.comp ((hT.iterate (k+m)).comp measurable_fst))

/-- The mass of the entire future fiber is measurable up to the ambient
null set on which intrinsic leaf measures may be chosen arbitrarily. -/
theorem aemeasurable_remainingFutureMass (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k = 0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q) (m : ℕ) :
    AEMeasurable (fun x => c.remainingTimeProduct hP hf μ x
      (c.remainingFutureAtom ell hell Q m x)) μ := by
  obtain ⟨κ, hκ, heq⟩ := c.exists_remainingTimeKernel d hP hf μ hA
  let := hκ
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ)
    (c.measurableSet_remainingFutureRelation hf ell hell Q hQ m)
  apply hm.aemeasurable.congr
  filter_upwards [heq] with x hx
  rw [hx]
  rfl

end EliminationChain
end DukePrimeDegree

end

end OAI
