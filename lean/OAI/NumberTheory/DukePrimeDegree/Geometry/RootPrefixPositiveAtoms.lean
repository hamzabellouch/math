import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureFibers
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureFiberEntropy

namespace OAI

/-! # Positive leaf mass of the present-and-future atom -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V : Type*} [TopologicalSpace V]

theorem presentFutureFiber_mem_nhds (C : RootPrefixCoordinates n P₀ V)
    (c : EliminationChain P₀ D) (hP₀ : InitialRootPattern P₀)
    (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    {M : ℕ} (T : X n → X n) (P : X n → Fin M)
    (z : (UpperRootTransverse n × V) × c.Time)
    (hgood : ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      P (T^[k] (rightAction (C.timeParam c hP₀ hf g z) ((completeRootChain n).word v))) =
        P (T^[k] (C.timeParam c hP₀ hf g z))) :
    ({t | P (C.timeParam c hP₀ hf g (z.1,t))=P (C.timeParam c hP₀ hf g z)} ∩
      futureFiber T P (C.timeParam c hP₀ hf g) z) ∈ 𝓝 z.2 := by
  have hfuture := C.futureFiber_mem_nhds c hP₀ hf g T P z hgood
  rw [←futureFiber_eq_iInter] at hfuture
  apply inter_mem _ hfuture
  have hc : Tendsto (c.fullRootTime hP₀ hf ∘ c.remainingRebase hP₀ hf z.2)
      (𝓝 z.2) (𝓝 (completeRootChain n).zeroTime) := by
    have H := ((c.continuous_fullRootTime hP₀ hf).comp
      (c.remainingRebase hP₀ hf z.2).continuous).tendsto z.2
    simpa only [Function.comp_apply,c.remainingRebase_self,c.fullRootTime_zero] using H
  filter_upwards [hc.eventually hgood] with t ht
  have H := ht 0
  simp only [Function.iterate_zero,Function.id_def,Function.comp_apply,c.word_fullRootTime] at H
  rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
  exact H

end RootPrefixCoordinates

theorem exists_cuts_with_positive_rootPrefix_presentFuture_atoms (d : ℕ)
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
          ({t | quotientCutObservation r j (C.timeParam c hP₀ hf g (z.1,t))=
            quotientCutObservation r j (C.timeParam c hP₀ hf g z)} ∩
            futureFiber (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
              (quotientCutObservation r j) (C.timeParam c hP₀ hf g) z) := by
  obtain ⟨r,hr,hgood⟩ := exists_observations_with_root_neighborhoods d ell hell ε hε hgap μ hA
  refine ⟨r,hr,?_⟩
  intro j
  filter_upwards [B.ae_coordinate_of_ambient μ hgood,B.ae_mem_conditionalKernel_support μ]
    with z hz hs
  apply ((B.conditionalKernel μ z.1).mem_support_iff_forall z.2).mp hs
  exact C.presentFutureFiber_mem_nhds c hP₀ hf g _ _ z (hz j)

end DukePrimeDegree

end

end OAI
