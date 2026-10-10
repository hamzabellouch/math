import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLeafSupport

namespace OAI

/-! # Everywhere locally finite versions of full upper-root kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def finiteUpperRootCubes {S : Type*} [MeasurableSpace S] (n : ℕ)
    (κ : Kernel S (UpperRootTime n)) : Set S :=
  {s | ∀ m : ℕ, κ s ((completeRootChain n).closedCube m) < ∞}

lemma measurableSet_finiteUpperRootCubes {S : Type*} [MeasurableSpace S] (n : ℕ)
    (κ : Kernel S (UpperRootTime n)) : MeasurableSet (finiteUpperRootCubes n κ) := by
  change MeasurableSet {s | ∀ m : ℕ, κ s ((completeRootChain n).closedCube m) < ∞}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun m => measurableSet_lt
    (κ.measurable_coe ((completeRootChain n).closedCube_compact m).measurableSet) measurable_const)

lemma locallyFinite_of_finite_upperRootCubes (n : ℕ) (ν : Measure (UpperRootTime n))
    (hν : ∀ m : ℕ, ν ((completeRootChain n).closedCube m) < ∞) : IsLocallyFiniteMeasure ν := by
  constructor
  intro t
  obtain ⟨m,hm⟩ := (completeRootChain n).mem_cube_exists 0 t
  simp only [zero_add] at hm
  exact ⟨(completeRootChain n).cube m, ((completeRootChain n).cube_open m).mem_nhds hm,
    (measure_mono ((completeRootChain n).cube_subset_closedCube m)).trans_lt (hν m)⟩

def locallyFiniteUpperRootVersion {S : Type*} [MeasurableSpace S] (n : ℕ)
    (κ : Kernel S (UpperRootTime n)) : Kernel S (UpperRootTime n) :=
  Kernel.piecewise (measurableSet_finiteUpperRootCubes n κ) κ 0

lemma locallyFiniteUpperRootVersion_eq {S : Type*} [MeasurableSpace S] (n : ℕ)
    (κ : Kernel S (UpperRootTime n)) (s : S) [IsLocallyFiniteMeasure (κ s)] :
    locallyFiniteUpperRootVersion n κ s = κ s := by
  apply ite_eq_left
  intro m
  exact ((completeRootChain n).closedCube_compact m).measure_lt_top

instance locallyFiniteUpperRootVersion_locallyFinite {S : Type*} [MeasurableSpace S]
    (n : ℕ) (κ : Kernel S (UpperRootTime n)) (s : S) :
    IsLocallyFiniteMeasure (locallyFiniteUpperRootVersion n κ s) := by
  change IsLocallyFiniteMeasure (if s ∈ finiteUpperRootCubes n κ then κ s else 0)
  split_ifs with hs
  · exact locallyFinite_of_finite_upperRootCubes n (κ s) hs
  · infer_instance

instance locallyFiniteUpperRootVersion_sFinite {S : Type*} [MeasurableSpace S]
    (n : ℕ) (κ : Kernel S (UpperRootTime n)) :
    IsSFiniteKernel (locallyFiniteUpperRootVersion n κ) := by
  apply isSFiniteKernel_of_finite_exhaustion _ (upperRootWindow n 0)
    (fun m => (upperRootWindow_open n 0 m).measurableSet) (upperRootWindow_cover n 0)
  intro s m
  have hsub : upperRootWindow n 0 m ⊆ (completeRootChain n).closedCube m := by
    simpa only [upperRootWindow, zero_add] using (completeRootChain n).cube_subset_closedCube m
  exact (measure_mono hsub).trans_lt ((completeRootChain n).closedCube_compact m).measure_lt_top

namespace UpperRootBox
variable {n : ℕ} {g : G n}

def regularLeafKernel (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) : Kernel (UpperRootTransverse n) (UpperRootTime n) :=
  locallyFiniteUpperRootVersion n (A.leafKernel R hAR μ hfree)

instance regularLeafKernel_locallyFinite (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) (s : UpperRootTransverse n) :
    IsLocallyFiniteMeasure (A.regularLeafKernel R hAR μ hfree s) :=
  locallyFiniteUpperRootVersion_locallyFinite _ _ _

instance regularLeafKernel_sFinite (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) : IsSFiniteKernel (A.regularLeafKernel R hAR μ hfree) :=
  locallyFiniteUpperRootVersion_sFinite _ _

lemma ae_regularLeafKernel_eq (A : UpperRootBox n g) (R : ℝ)
    (hAR : A.time ⊆ upperRootWindow n R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      A.regularLeafKernel R hAR μ hfree s = A.leafMeasure R μ s := by
  filter_upwards [A.ae_leafMeasure_spec R hAR μ hfree, A.ae_leafKernel_eq R hAR μ hfree]
    with s hs he
  have : IsLocallyFiniteMeasure (A.leafKernel R hAR μ hfree s) := he.symm ▸ hs.1
  exact (locallyFiniteUpperRootVersion_eq _ _ s).trans he

end UpperRootBox
end DukePrimeDegree

end

end OAI
