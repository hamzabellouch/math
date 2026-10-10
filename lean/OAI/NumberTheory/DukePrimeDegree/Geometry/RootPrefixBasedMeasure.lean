import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRegularKernel
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRebase

namespace OAI

/-! # Measurable remaining-subgroup leaves based at the sampled point -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def centeredRemainingKernel {S : Type*} [MeasurableSpace S]
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (κ : Kernel S c.Time) [IsSFiniteKernel κ] :
    Kernel (S × c.Time) c.Time where
  toFun z := c.centeredRemainingMeasure hP hfinal (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    have H := Kernel.measurable_kernel_prodMk_left (κ := Kernel.prodMkRight c.Time κ)
      (((c.continuous_remainingRebase hP hfinal).measurable.comp
        (measurable_fst.snd.prodMk measurable_snd)) hU)
    convert H using 1
    funext z
    exact Measure.map_apply (c.remainingRebase hP hfinal z.2).measurable hU

def basedRemainingKernel {S : Type*} [MeasurableSpace S]
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (κ : Kernel S c.Time) [IsSFiniteKernel κ] :
    Kernel (S × c.Time) c.Time where
  toFun z := c.basedRemainingMeasure hP hfinal (κ z.1) z.2
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    change Measurable (fun z =>
      (c.centeredRemainingKernel hP hfinal κ z (c.cube 1))⁻¹ *
        c.centeredRemainingKernel hP hfinal κ z U)
    exact (c.centeredRemainingKernel hP hfinal κ |>.measurable_coe
      (c.cube_open 1).measurableSet).inv.mul
        (c.centeredRemainingKernel hP hfinal κ |>.measurable_coe hU)

lemma groupLeafMeasure_centered (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) (t : c.Time) :
    c.remainingGroupLeafMeasure hP hfinal (c.centeredRemainingMeasure hP hfinal ν t) =
      (c.remainingGroupLeafMeasure hP hfinal ν).map
        (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hfinal t)⁻¹) := by
  rw [remainingGroupLeafMeasure,centeredRemainingMeasure,
    Measure.map_map (c.remainingWordHomeomorph hP hfinal).measurable
      (c.remainingRebase hP hfinal t).measurable,
    remainingGroupLeafMeasure,
    Measure.map_map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hfinal t)⁻¹).measurable
      (c.remainingWordHomeomorph hP hfinal).measurable]
  congr 1
  funext u
  exact c.remainingRebase_word hP hfinal t u

end EliminationChain
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T]

lemma timeParam_rebased (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (g : G n) (s : UpperRootTransverse n × T) (t u : c.Time) :
    C.timeParam c hP hfinal g (s,u) =
      rightAction (C.timeParam c hP hfinal g (s,t))
        (c.word (c.remainingRebase hP hfinal t u)) := by
  rw [C.timeParam_eq_action,C.timeParam_eq_action,rightAction_mul]
  congr 1
  have he := congrArg Subtype.val (c.remainingRebase_word hP hfinal t u)
  change c.word (c.remainingRebase hP hfinal t u) = (c.word t)⁻¹ * c.word u at he
  rw [he,mul_inv_cancel_left]

end RootPrefixCoordinates
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

def basedLeaf (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse n × T) × c.Time) : Measure c.Time :=
  c.basedRemainingMeasure hP hfinal (A.leafMeasure R μ z.1) z.2

lemma aemeasurable_basedLeaf (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    AEMeasurable (A.basedLeaf R μ) (A.coordinateMeasure μ) := by
  have he : ∀ᵐ z ∂A.coordinateMeasure μ,
      A.regularLeafKernel R hAR μ hfree z.1 = A.leafMeasure R μ z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (A.ae_regularLeafKernel_eq R hAR μ hfree)
  exact (c.basedRemainingKernel hP hfinal (A.regularLeafKernel R hAR μ hfree)).measurable.aemeasurable.congr
    (he.mono fun z hz => congrArg (fun ν => c.basedRemainingMeasure hP hfinal ν z.2) hz)

theorem ae_basedLeaf_spec (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ, IsLocallyFiniteMeasure (A.basedLeaf R μ z) ∧
      A.basedLeaf R μ z (c.cube 1) = 1 := by
  have hlf : ∀ᵐ z ∂A.coordinateMeasure μ, IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) :=
    ae_of_ae_map measurable_fst.aemeasurable
      ((A.ae_leafMeasure_spec R hAR μ hfree).mono fun s hs => hs.1)
  filter_upwards [hlf,A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz ht
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hz
  exact ⟨c.basedRemainingMeasure_locallyFinite hP hfinal _ _ ht,
    c.basedRemainingMeasure_unit hP hfinal _ _ ht⟩

end RootPrefixBox
end DukePrimeDegree

end

end OAI
