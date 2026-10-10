import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteFutureCodes
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootAdaptedObservations
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootCoordinatesMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootMeasureCovariance
import OAI.NumberTheory.PrimePackets.KernelSupport

namespace OAI

/-! # Positive conditional mass of whole future fibers in upper-root boxes -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRootTranslate_zero (n : ℕ) (t : UpperRootTime n) :
    upperRootTranslate n t (completeRootChain n).zeroTime=t := by
  apply (upperRootWordHomeomorph n).injective
  rw [upperRootWord_translate,upperRootWord_zero,mul_one]

lemma upperRootQuotientParam_translate (n : ℕ) (g : G n)
    (s : UpperRootTransverse n) (t v : UpperRootTime n) :
    upperRootQuotientParam n g (s,upperRootTranslate n t v) =
      rightAction (upperRootQuotientParam n g (s,t)) ((completeRootChain n).word v) := by
  have he := congrArg Subtype.val (upperRootWord_translate n t v)
  change (completeRootChain n).word (upperRootTranslate n t v) =
    (completeRootChain n).word t * (completeRootChain n).word v at he
  rw [upperRootQuotientParam_eq_action,upperRootQuotientParam_eq_action,rightAction_mul,he]

lemma upperRoot_future_fiber_nhds {n M : ℕ} (g : G n)
    (T : X n → X n) (P : X n → Fin M)
    (z : UpperRootTransverse n × UpperRootTime n)
    (hgood : ∀ᶠ v in 𝓝 (completeRootChain n).zeroTime, ∀ k : ℕ,
      P (T^[k] (rightAction (upperRootQuotientParam n g z) ((completeRootChain n).word v))) =
        P (T^[k] (upperRootQuotientParam n g z))) :
    (⋂ k, labelFiber (fun z => finiteFutureCode T P k (upperRootQuotientParam n g z)) z) ∈
      𝓝 z.2 := by
  let τ := upperRootTranslate n z.2
  have hz : τ.symm z.2 = (completeRootChain n).zeroTime := by
    rw [←upperRootTranslate_zero n z.2]
    exact τ.symm_apply_apply _
  have hc : Tendsto τ.symm (𝓝 z.2) (𝓝 (completeRootChain n).zeroTime) := by
    simpa only [hz] using τ.symm.continuous.tendsto z.2
  filter_upwards [hc.eventually hgood] with t ht
  apply mem_iInter.mpr
  have he : upperRootQuotientParam n g (z.1,t) =
      rightAction (upperRootQuotientParam n g z) ((completeRootChain n).word (τ.symm t)) := by
    simpa only [τ,Homeomorph.apply_symm_apply] using
      upperRootQuotientParam_translate n g z.1 z.2 (τ.symm t)
  have H := (all_finiteFutureCode_eq_iff T P
    (upperRootQuotientParam n g (z.1,t)) (upperRootQuotientParam n g z)).mpr
      (fun k => by rw [he]; exact ht (k+1))
  exact H

namespace UpperRootBox
variable {n : ℕ} {g : G n}

theorem ae_mem_conditionalKernel_support (B : UpperRootBox n g)
    (μ : Measure (X n)) [IsFiniteMeasure μ] :
    ∀ᵐ z ∂B.coordinateMeasure μ, z.2 ∈ (B.conditionalKernel μ z.1).support := by
  have H : ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ (B.conditionalKernel μ s).support :=
    ae_of_all _ fun s => (B.conditionalKernel μ s).support_mem_ae
  have H' := Measure.ae_compProd_of_ae_ae
    (measurableSet_kernel_support_secondCountable (B.conditionalKernel μ)) H
  simpa only [conditionalKernel,Measure.disintegrate] using H'

end UpperRootBox

theorem exists_cuts_with_positive_future_fibers (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (g : G (d+1)) (B : UpperRootBox (d+1) g) :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ j : ℕ, ∀ᵐ z ∂B.coordinateMeasure μ,
        0 < B.conditionalKernel μ z.1
          (⋂ k, labelFiber (fun z => finiteFutureCode
            (fun x => rightAction x (diagonalOneParameter ell hell (-1)))
            (quotientCutObservation r j) k (upperRootQuotientParam (d+1) g z)) z) := by
  obtain ⟨r,hr,hgood⟩ := exists_observations_with_root_neighborhoods d ell hell ε hε hgap μ hA
  refine ⟨r,hr,?_⟩
  intro j
  filter_upwards [B.ae_coordinate_of_ambient μ hgood,B.ae_mem_conditionalKernel_support μ]
    with z hz hs
  apply ((B.conditionalKernel μ z.1).mem_support_iff_forall z.2).mp hs
  exact upperRoot_future_fiber_nhds g _ _ z (hz j)

end DukePrimeDegree

end

end OAI
