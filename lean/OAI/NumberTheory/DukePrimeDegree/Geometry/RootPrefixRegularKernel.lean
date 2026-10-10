import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLeafSupport

namespace OAI

/-! # Everywhere locally finite versions of remaining-subgroup kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def finiteRemainingCubes {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) : Set S :=
  {s | ∀ m : ℕ, κ s (c.closedCube m) < ∞}

lemma measurableSet_finiteRemainingCubes {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) : MeasurableSet (finiteRemainingCubes c κ) := by
  change MeasurableSet {s | ∀ m : ℕ, κ s (c.closedCube m) < ∞}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun m => measurableSet_lt
    (κ.measurable_coe (c.closedCube_compact m).measurableSet) measurable_const)

lemma locallyFinite_of_finite_remainingCubes (c : EliminationChain P D) (ν : Measure (c.Time))
    (hν : ∀ m : ℕ, ν (c.closedCube m) < ∞) : IsLocallyFiniteMeasure ν := by
  constructor
  intro t
  obtain ⟨m,hm⟩ := c.mem_cube_exists 0 t
  simp only [zero_add] at hm
  exact ⟨c.cube m, (c.cube_open m).mem_nhds hm,
    (measure_mono (c.cube_subset_closedCube m)).trans_lt (hν m)⟩

def locallyFiniteRemainingVersion {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) : Kernel S (c.Time) :=
  Kernel.piecewise (measurableSet_finiteRemainingCubes c κ) κ 0

lemma locallyFiniteRemainingVersion_eq {S : Type*} [MeasurableSpace S] (c : EliminationChain P D)
    (κ : Kernel S (c.Time)) (s : S) [IsLocallyFiniteMeasure (κ s)] :
    locallyFiniteRemainingVersion c κ s = κ s := by
  apply ite_eq_left
  intro m
  exact (c.closedCube_compact m).measure_lt_top

instance locallyFiniteRemainingVersion_locallyFinite {S : Type*} [MeasurableSpace S]
    (c : EliminationChain P D) (κ : Kernel S (c.Time)) (s : S) :
    IsLocallyFiniteMeasure (locallyFiniteRemainingVersion c κ s) := by
  change IsLocallyFiniteMeasure (if s ∈ finiteRemainingCubes c κ then κ s else 0)
  split_ifs with hs
  · exact locallyFinite_of_finite_remainingCubes c (κ s) hs
  · infer_instance

instance locallyFiniteRemainingVersion_sFinite {S : Type*} [MeasurableSpace S]
    (c : EliminationChain P D) (κ : Kernel S (c.Time)) :
    IsSFiniteKernel (locallyFiniteRemainingVersion c κ) := by
  apply isSFiniteKernel_of_finite_exhaustion _ (c.remainingWindow 0)
    (fun m => (c.remainingWindow_open 0 m).measurableSet) (c.remainingWindow_cover 0)
  intro s m
  have hsub : c.remainingWindow 0 m ⊆ c.closedCube m := by
    simpa only [EliminationChain.remainingWindow, zero_add] using c.cube_subset_closedCube m
  exact (measure_mono hsub).trans_lt (c.closedCube_compact m).measure_lt_top

namespace RootPrefixBox
variable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

def regularLeafKernel (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) : Kernel ((UpperRootTransverse n × T)) (c.Time) :=
  locallyFiniteRemainingVersion c (A.leafKernel R hAR μ hfree)

instance regularLeafKernel_locallyFinite (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) (s : (UpperRootTransverse n × T)) :
    IsLocallyFiniteMeasure (A.regularLeafKernel R hAR μ hfree s) :=
  locallyFiniteRemainingVersion_locallyFinite _ _ _

instance regularLeafKernel_sFinite (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) : IsSFiniteKernel (A.regularLeafKernel R hAR μ hfree) :=
  locallyFiniteRemainingVersion_sFinite _ _

lemma ae_regularLeafKernel_eq (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.regularLeafKernel R hAR μ hfree s = A.leafMeasure R μ s := by
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree, A.ae_leafKernel_eq R hAR μ hfree]
    with s hs he
  have : IsLocallyFiniteMeasure (A.leafKernel R hAR μ hfree s) := he.symm ▸ hs.1
  exact (locallyFiniteRemainingVersion_eq _ _ s).trans he

end RootPrefixBox
end DukePrimeDegree

end

end OAI
