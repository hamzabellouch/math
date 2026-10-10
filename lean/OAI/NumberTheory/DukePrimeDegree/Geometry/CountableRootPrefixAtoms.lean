import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureFibers

namespace OAI

/-! # Positive leaf mass of countable whole-future atoms

The argument uses support of the actual conditional leaf kernel. No finite
entropy of the countable observation is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V A : Type*} [TopologicalSpace V]

theorem wholeFutureAtom_mem_nhds (C : RootPrefixCoordinates n P₀ V)
    (c : EliminationChain P₀ D) (hP₀ : InitialRootPattern P₀)
    (hf : c.finalEntries = allPositiveRoots n) (g : G n)
    (T : X n → X n) (Q : X n → A)
    (z : (UpperRootTransverse n × V) × c.Time)
    (hgood : ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction (C.timeParam c hP₀ hf g z) ((completeRootChain n).word v))) =
        Q (T^[k] (C.timeParam c hP₀ hf g z))) :
    {t | ∀ k : ℕ, Q (T^[k] (C.timeParam c hP₀ hf g (z.1,t))) =
      Q (T^[k] (C.timeParam c hP₀ hf g z))} ∈ 𝓝 z.2 := by
  have hc : Tendsto (c.fullRootTime hP₀ hf ∘ c.remainingRebase hP₀ hf z.2)
      (𝓝 z.2) (𝓝 (completeRootChain n).zeroTime) := by
    have H := ((c.continuous_fullRootTime hP₀ hf).comp
      (c.remainingRebase hP₀ hf z.2).continuous).tendsto z.2
    simpa only [Function.comp_apply,c.remainingRebase_self,c.fullRootTime_zero] using H
  filter_upwards [hc.eventually hgood] with t ht
  intro k
  rw [Function.comp_apply,c.word_fullRootTime] at ht
  rw [C.timeParam_rebased c hP₀ hf g z.1 z.2 t]
  exact ht k

end RootPrefixCoordinates

namespace RootPrefixBox
variable {n : ℕ} {P₀ : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {V A : Type*} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  {C : RootPrefixCoordinates n P₀ V} {c : EliminationChain P₀ D}
  {hP₀ : InitialRootPattern P₀} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

omit [SecondCountableTopology V] in
theorem ae_wholeFutureAtom_pos (B : RootPrefixBox C c hP₀ hf g)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (T : X n → X n) (Q : X n → A)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain n).word v))) = Q (T^[k] x)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, 0 < B.conditionalKernel μ z.1
      {t | ∀ k : ℕ, Q (T^[k] (C.timeParam c hP₀ hf g (z.1,t))) =
        Q (T^[k] (C.timeParam c hP₀ hf g z))} := by
  filter_upwards [B.ae_coordinate_of_ambient μ hgood,B.ae_mem_conditionalKernel_support μ]
    with z hz hs
  apply ((B.conditionalKernel μ z.1).mem_support_iff_forall z.2).mp hs
  exact C.wholeFutureAtom_mem_nhds c hP₀ hf g T Q z hz

end RootPrefixBox
end DukePrimeDegree

end

end OAI
