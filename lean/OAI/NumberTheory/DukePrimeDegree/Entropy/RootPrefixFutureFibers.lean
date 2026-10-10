import OAI.NumberTheory.DukePrimeDegree.Entropy.UpperRootFutureFibers
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBasedMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRestrictions

namespace OAI

/-! # Positive future fibers for the remaining-root product charts -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def fullRootTime (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) : UpperRootTime n :=
  (upperRootWordHomeomorph n).symm
    ⟨(c.remainingWordHomeomorph hP hf t).val,
      positiveRootGeneratedGroup_mono Finset.sdiff_subset
        (c.remainingWordHomeomorph hP hf t).prop⟩

lemma continuous_fullRootTime (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) : Continuous (c.fullRootTime hP hf) :=
  (upperRootWordHomeomorph n).symm.continuous.comp
    ((continuous_subtype_val.comp (c.remainingWordHomeomorph hP hf).continuous).subtype_mk _)

lemma fullRootTime_zero (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) :
    c.fullRootTime hP hf c.zeroTime = (completeRootChain n).zeroTime := by
  apply (upperRootWordHomeomorph n).injective
  rw [fullRootTime,Homeomorph.apply_symm_apply,upperRootWord_zero]
  apply Subtype.ext
  exact c.word_zeroTime

lemma word_fullRootTime (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    (completeRootChain n).word (c.fullRootTime hP hf t) = c.word t :=
  congrArg Subtype.val ((upperRootWordHomeomorph n).apply_symm_apply _)

end EliminationChain

namespace RootPrefixCoordinates
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V : Type*} [TopologicalSpace V]

theorem futureFiber_mem_nhds (C : RootPrefixCoordinates n P₀ V)
    (c : EliminationChain P₀ D) (hP₀ : InitialRootPattern P₀)
    (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    {M : ℕ} (T : X n → X n) (P : X n → Fin M)
    (z : (UpperRootTransverse n × V) × c.Time)
    (hgood : ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      P (T^[k] (rightAction (C.timeParam c hP₀ hf g z) ((completeRootChain n).word v))) =
        P (T^[k] (C.timeParam c hP₀ hf g z))) :
    (⋂ k, labelFiber (fun z => finiteFutureCode T P k (C.timeParam c hP₀ hf g z)) z) ∈
      𝓝 z.2 := by
  have hc : Tendsto (c.fullRootTime hP₀ hf ∘ c.remainingRebase hP₀ hf z.2)
      (𝓝 z.2) (𝓝 (completeRootChain n).zeroTime) := by
    have H := ((c.continuous_fullRootTime hP₀ hf).comp
      (c.remainingRebase hP₀ hf z.2).continuous).tendsto z.2
    simpa only [Function.comp_apply,c.remainingRebase_self,c.fullRootTime_zero] using H
  filter_upwards [hc.eventually hgood] with t ht
  apply mem_iInter.mpr
  apply (all_finiteFutureCode_eq_iff T P _ _).mpr
  intro k
  rw [Function.comp_apply,c.word_fullRootTime] at ht
  rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
  exact ht (k+1)

end RootPrefixCoordinates

namespace RootPrefixBox
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  {C : RootPrefixCoordinates n P₀ V} {c : EliminationChain P₀ D}
  {hP₀ : InitialRootPattern P₀} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

omit [SecondCountableTopology V] in
theorem ae_mem_conditionalKernel_support (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ z ∂B.coordinateMeasure μ, z.2 ∈ (B.conditionalKernel μ z.1).support := by
  have H : ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ (B.conditionalKernel μ s).support :=
    ae_of_all _ fun s => (B.conditionalKernel μ s).support_mem_ae
  have H' := Measure.ae_compProd_of_ae_ae
    (measurableSet_kernel_support_secondCountable (B.conditionalKernel μ)) H
  simpa only [conditionalKernel,Measure.disintegrate] using H'

end RootPrefixBox

theorem exists_cuts_with_positive_rootPrefix_future_fibers (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    (C : RootPrefixCoordinates (d+1) P₀ V) (c : EliminationChain P₀ D)
    (hP₀ : InitialRootPattern P₀) (hf : c.finalEntries = allPositiveRoots (d+1))
    (g : G (d+1)) (B : RootPrefixBox C c hP₀ hf g) :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ j : ℕ, ∀ᵐ z ∂B.coordinateMeasure μ,
        0 < B.conditionalKernel μ z.1
          (⋂ k, labelFiber (fun z => finiteFutureCode
            (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
            (quotientCutObservation r j) k (C.timeParam c hP₀ hf g z)) z) := by
  obtain ⟨r,hr,hgood⟩ := exists_observations_with_root_neighborhoods d ell hell ε hε hgap μ hA
  refine ⟨r,hr,?_⟩
  intro j
  filter_upwards [B.ae_coordinate_of_ambient μ hgood,B.ae_mem_conditionalKernel_support μ]
    with z hz hs
  apply ((B.conditionalKernel μ z.1).mem_support_iff_forall z.2).mp hs
  exact C.futureFiber_mem_nhds c hP₀ hf g _ _ z (hz j)

end DukePrimeDegree

end

end OAI
