import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.BoundedFutureMass

namespace OAI

/-! # A probability kernel on the entire subordinate future

The intrinsic product has an s-finite measurable version. Restricting it
on the jointly measurable future relation and normalizing gives an actual
probability kernel. On the exceptional zero/infinite-mass set we use a
point mass; the intrinsic formula holds almost everywhere whenever the
proved positive finite future-mass condition applies.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

private def futureRestrictedKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) : Kernel (X n) c.Time where
  toFun x := (κ x).restrict (c.remainingFutureAtom ell hell Q m x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    simp_rw [Measure.restrict_apply hA]
    exact Kernel.measurable_kernel_prodMk_left
      ((measurable_snd hA).inter (c.measurableSet_remainingFutureRelation hf ell hell Q hQ m))

private def futureNormalizedKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) : Kernel (X n) c.Time where
  toFun x :=
    let ν := c.futureRestrictedKernel hf κ ell hell Q hQ m x
    (ν univ)⁻¹ • ν
  measurable' := by
    let ν := c.futureRestrictedKernel hf κ ell hell Q hQ m
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun x => (ν x univ)⁻¹ * ν x A)
    exact (ν.measurable_coe MeasurableSet.univ).inv.mul (ν.measurable_coe hA)

/-- Normalize where the full-future mass is positive finite, using a
fixed point mass on the remaining measurable exceptional set. -/
def wholeFutureProbabilityKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) : Kernel (X n) c.Time :=
  let ν := c.futureRestrictedKernel hf κ ell hell Q hQ m
  have hgood : MeasurableSet {x | ν x univ ≠ 0 ∧ ν x univ ≠ ∞} :=
    (measurableSet_eq_fun (ν.measurable_coe MeasurableSet.univ) measurable_const).compl.inter
      (measurableSet_eq_fun (ν.measurable_coe MeasurableSet.univ) measurable_const).compl
  Kernel.piecewise hgood
    (c.futureNormalizedKernel hf κ ell hell Q hQ m)
    (Kernel.const (X n) (Measure.dirac c.zeroTime))

instance wholeFutureProbabilityKernel_markov (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) :
    IsMarkovKernel (c.wholeFutureProbabilityKernel hf κ ell hell Q hQ m) := by
  refine ⟨fun x => ⟨?_⟩⟩
  change (if (c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ ≠ 0 ∧
      (c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ ≠ ∞ then
      c.futureNormalizedKernel hf κ ell hell Q hQ m x else Measure.dirac c.zeroTime) univ = 1
  split_ifs with hx
  · change ((c.futureRestrictedKernel hf κ ell hell Q hQ m x univ)⁻¹ •
      c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ = 1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hx.1 hx.2
  · simp

lemma wholeFutureProbabilityKernel_apply (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0) (Q : X n → ℕ)
    (hQ : Measurable Q) (m : ℕ) (x : X n)
    (hpos : κ x (c.remainingFutureAtom ell hell Q m x) ≠ 0)
    (hfin : κ x (c.remainingFutureAtom ell hell Q m x) ≠ ∞) :
    c.wholeFutureProbabilityKernel hf κ ell hell Q hQ m x =
      (anchorNormalize (κ x) (c.remainingFutureAtom ell hell Q m x)).restrict
        (c.remainingFutureAtom ell hell Q m x) := by
  have hmass : c.futureRestrictedKernel hf κ ell hell Q hQ m x univ =
      κ x (c.remainingFutureAtom ell hell Q m x) := by
    exact Measure.restrict_apply_univ _
  change (if (c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ ≠ 0 ∧
      (c.futureRestrictedKernel hf κ ell hell Q hQ m x) univ ≠ ∞ then
      c.futureNormalizedKernel hf κ ell hell Q hQ m x else Measure.dirac c.zeroTime) = _
  rw [ite_eq_left (by simpa only [hmass] using And.intro hpos hfin)]
  change (c.futureRestrictedKernel hf κ ell hell Q hQ m x univ)⁻¹ •
    (κ x).restrict (c.remainingFutureAtom ell hell Q m x) = _
  rw [hmass, anchorNormalize, Measure.restrict_smul]

theorem exists_wholeFutureProbabilityKernel (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q) (m : ℕ)
    (hmass : ∀ᵐ x ∂μ,
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x) ≠ 0 ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q m x) ≠ ∞) :
    ∃ κ : Kernel (X (d+1)) c.Time, IsMarkovKernel κ ∧
      ∀ᵐ x ∂μ, κ x =
        (anchorNormalize (c.remainingTimeProduct hP hf μ x)
          (c.remainingFutureAtom ell hell Q m x)).restrict
          (c.remainingFutureAtom ell hell Q m x) := by
  obtain ⟨κ,hκ,heq⟩ := c.exists_remainingTimeKernel d hP hf μ hA
  let := hκ
  refine ⟨c.wholeFutureProbabilityKernel hf κ ell hell Q hQ m,inferInstance,?_⟩
  filter_upwards [heq,hmass] with x hx hm
  rw [c.wholeFutureProbabilityKernel_apply hf κ ell hell Q hQ m x]
  · rw [hx]
  · rw [hx]; exact hm.1
  · rw [hx]; exact hm.2

/-- Push a time-coordinate kernel to the actual right root orbits. -/
def futureAmbientKernel (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsSFiniteKernel κ] : Kernel (X n) (X n) where
  toFun x := (κ x).map (fun u => rightAction x (c.word u))
  measurable' := by
    have hF : Measurable (fun z : X n × c.Time => rightAction z.1 (c.word z.2)) :=
      (continuous_rightAction_uncurry n).measurable.comp
        (measurable_fst.prodMk ((c.word_isEmbedding_remaining hf).continuous.measurable.comp
          measurable_snd))
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    change Measurable (fun x => ((κ x).map (fun u => rightAction x (c.word u))) A)
    have heq (x : X n) : ((κ x).map (fun u => rightAction x (c.word u))) A =
        κ x ((fun u => rightAction x (c.word u)) ⁻¹' A) :=
      Measure.map_apply (hF.comp measurable_prodMk_left) hA
    simp_rw [heq]
    exact Kernel.measurable_kernel_prodMk_left (hF hA)

instance futureAmbientKernel_markov (c : EliminationChain P D)
    (hf : c.finalEntries = allPositiveRoots n)
    (κ : Kernel (X n) c.Time) [IsMarkovKernel κ] :
    IsMarkovKernel (c.futureAmbientKernel hf κ) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  change (κ x).map (fun u => rightAction x (c.word u)) univ = 1
  rw [Measure.map_apply hF MeasurableSet.univ,Set.preimage_univ,measure_univ]

lemma ae_wholeFutureKernel_same_names (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0) (Q : X (d+1) → ℕ)
    (hQ : Measurable Q) (m : ℕ) (κ : Kernel (X (d+1)) c.Time) [IsMarkovKernel κ]
    (hversion : ∀ᵐ x ∂μ, κ x =
      (anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q m x)).restrict
        (c.remainingFutureAtom ell hell Q m x)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂c.futureAmbientKernel hf κ x,
      ∀ k : ℕ,
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] y) =
        Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] x) := by
  filter_upwards [hversion] with x hx
  change ∀ᵐ y ∂(κ x).map (fun u => rightAction x (c.word u)), _
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  apply (ae_map_iff hF.aemeasurable ?_).mpr
  · rw [hx]
    exact ae_restrict_mem (c.measurableSet_remainingFutureAtom hf ell hell Q hQ m x)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact (hQ.comp (((continuous_rightAction _).measurable).iterate (k+m)))
      (measurableSet_singleton _)

end EliminationChain
/-- The constructed low-height-entropy observation has a measurable
probability-kernel version of its normalized whole-future root measures.
Stationarity with respect to the ambient measure is a separate assertion. -/
theorem exists_low_entropy_wholeFutureProbabilityKernel (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (hgap : ∀ p : allPositiveRoots (d+1), Real.log 4 ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (H Q : X (d+1) → ℕ) (κ : Kernel (X (d+1)) (UpperRootTime (d+1))),
      Measurable H ∧ Measurable Q ∧ IsMarkovKernel κ ∧
      (∀ m, IsCompact {x | H x ≤ m}) ∧
      (∀ m, (Q '' {x | H x ≤ m}).Finite) ∧
      (∀ N, observationEntropyRate μ
        (fun x => rightAction x (diagonalOneParameter ell hell (-1))) (heightClip H N) < ε) ∧
      ∀ᵐ x ∂μ,
        let c := completeRootChain (d+1)
        let ν := c.remainingTimeProduct
          (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ x
        κ x = (anchorNormalize ν (c.remainingFutureAtom ell hell Q 0 x)).restrict
          (c.remainingFutureAtom ell hell Q 0 x) := by
  obtain ⟨H,Q,hH,hQ,hcompact,hfinite,hent,hmass⟩ :=
    exists_low_entropy_positive_future_mass d ell hell hgap μ hε
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨κ,hκ,hversion⟩ := EliminationChain.exists_wholeFutureProbabilityKernel d
    (completeRootChain (d+1)) (by intro p hp; simp at hp)
    (completeRootChain_final (d+1)) μ hA ell hell Q hQ 0 (by
      filter_upwards [hmass] with x hx
      exact ⟨hx.1.ne',ne_top_of_le_ne_top ENNReal.one_ne_top hx.2⟩)
  exact ⟨H,Q,κ,hH,hQ,hκ,hcompact,hfinite,hent,hversion⟩

end DukePrimeDegree

end

end OAI
