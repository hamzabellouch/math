import OAI.NumberTheory.DukePrimeDegree.Geometry.RootTransverseRectangles

namespace OAI

/-! # Unconditional local product boxes at every ordered-root step -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

instance positiveRootGeneratedGroup_secondCountable {n : ℕ} (S : Finset (Fin n × Fin n)) :
    SecondCountableTopology (positiveRootGeneratedGroup S) := by
  let : SecondCountableTopology (G n) := inferInstance
  exact TopologicalSpace.secondCountableTopology_induced _ (G n) Subtype.val

instance initialRemainingErase_standardBorel {n : ℕ} (q : InitialRootStep n) :
    StandardBorelSpace (positiveRootGeneratedGroup (q.remaining.erase q.root)) := by
  have hcomp : ∀ a b c : Fin n, (a,b) ∈ q.remaining.erase q.root →
      (b,c) ∈ q.remaining.erase q.root → (a,c) ∈ q.remaining.erase q.root := by
    dsimp only [InitialRootStep.remaining]
    rw [initialRemaining_erase]
    exact initialRemaining_roots_closed _
      (initialRootPattern_insert_min q.initial q.root q.mem_remaining q.least)
  exact (isClosed_positiveRootGeneratedGroup _
    (fun p hp => q.remaining_positive p (Finset.mem_of_mem_erase hp)) hcomp).measurableSet.standardBorel

namespace RootPrefixCoordinates
variable {n : ℕ} (q : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n q.processed T) (g : G n) (k : Fin n)

def factorTime (z : C.factorPivotDomain q g k) : ℝ :=
  rootParameter q.root.1 q.root.2 k (C.factorBase q g z.val)

lemma continuous_factorTime : Continuous (C.factorTime q g k) := by
  have hp : Continuous (C.factorPivot q g k) :=
    ((C.continuous_factorBase q g).comp continuous_subtype_val).subtype_mk _
  exact continuous_rootParameter.comp hp

def rectangleSlice (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × Q.second → RootSlice q.root.1 q.root.2 k := C.factorSlice q g k ∘ Q.inclusion

def rectangleTime (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Q.first × Q.second → ℝ := C.factorTime q g k ∘ Q.inclusion

lemma rectangleSlice_isOpenEmbedding (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Topology.IsOpenEmbedding (C.rectangleSlice q g k Q) :=
  (C.factorSlice_isOpenEmbedding q g k).comp
    (Q.inclusion_isOpenEmbedding (C.factorPivotDomain_open q g k))

lemma continuous_rectangleTime (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Continuous (C.rectangleTime q g k Q) :=
  (C.continuous_factorTime q g k).comp
    (Q.inclusion_isOpenEmbedding (C.factorPivotDomain_open q g k)).continuous

lemma rectangleSlice_orbit (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (s : Q.first) (w : Q.second) (t : ℝ) :
    rootQuotientParametrization q.distinct (C.rectangleSlice q g k Q (s,w),t) =
      rightAction (Quotient.mk _ ((g * s.val.1.val) * C.base s.val.2))
        (w.val.val * Matrix.SpecialLinearGroup.transvection q.distinct
          (t - C.rectangleTime q g k Q (s,w))) :=
  C.factorSlice_orbit q g k (Q.inclusion (s,w)) t

end RootPrefixCoordinates

theorem remainingRootBox_conditional_product
    (d : ℕ) (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hcover : A.transverse ⊆ Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      (σ.condKernel s).restrict (univ ×ˢ J) =
        ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν := by
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  exact initialRootChart_shifted_conditional_product d q A R hAR μ hA σ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    (shiftedRootFactorPullback_map q.distinct A μ _
      (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding _
      (C.continuous_rectangleTime q g k Q).measurable hcover)
    (fun s => Quotient.mk _ ((g * s.val.1.val) * C.base s.val.2))
    (fun w => w.val) (C.rectangleSlice_orbit q g k Q) J hJ
      (Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun w => hwindow (s,w))

theorem exists_remainingRoot_product_box
    (d : ℕ) (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    (z : C.factorPivotDomain q g k) (t : ℝ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ Q : RootTransverseRectangle (C.factorPivotDomain q g k), ∃ hQ : Nonempty Q.second,
      letI := hQ
      haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
      ∃ (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ),
        IsOpen J ∧ z.val ∈ Q.first ×ˢ Q.second ∧ t ∈ J ∧
        A.time ⊆ rootLeafWindow R 0 ∧
        let σ := shiftedRootFactorPullback q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
        haveI := shiftedRootFactorPullback_finite q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
          (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
        ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
          (σ.condKernel s).restrict (univ ×ˢ J) =
            ((σ.condKernel s).restrict (univ ×ˢ J)).fst.prod ν := by
  obtain ⟨Q,A,R,J,hJ,hz,ht,hcover,hbound,hw⟩ := exists_shifted_root_rectangle
    (C.factorPivotDomain_open q g k) q.distinct (C.factorSlice q g k)
    (C.factorSlice_isOpenEmbedding q g k) (C.factorTime q g k)
    (C.continuous_factorTime q g k) z t
  let : Nonempty Q.second := ⟨⟨z.val.2,hz.2⟩⟩
  refine ⟨Q,inferInstance,A,R,J,hJ,hz,ht,hbound,?_⟩
  apply remainingRootBox_conditional_product d q C g k Q A R hbound
    (by rw [hcover]; exact subset_rfl) J hJ.measurableSet hw μ hA

end DukePrimeDegree

end

end OAI
