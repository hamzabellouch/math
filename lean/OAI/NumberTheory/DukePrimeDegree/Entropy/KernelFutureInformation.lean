import OAI.NumberTheory.DukePrimeDegree.Entropy.StationaryFiberConditioning
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureMap
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureBlockConditionalInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformationLowerBound

namespace OAI

/-! # The actual root information is bounded by full metric entropy

The entire future is an almost sure fiber label of the constructed
kernel. Adding that label to the conditioning sigma algebra leaves its
conditional law unchanged, and makes the future inclusion literal.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

theorem ambientFutureMeasure_ae_same_names
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (ell : Fin n → ℝ) (hell : ∑ k, ell k=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (m : ℕ) (x : X n) :
    ∀ᵐ y ∂c.ambientFutureMeasure hP hf μ ell hell Q m x, ∀ k : ℕ,
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] y) =
      Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k+m] x) := by
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry n).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  unfold ambientFutureMeasure
  apply (ae_map_iff hF.aemeasurable ?_).mpr
  · exact ae_restrict_mem (c.measurableSet_remainingFutureAtom hf ell hell Q hQ m x)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact (hQ.comp (((continuous_rightAction _).measurable).iterate (k+m)))
      (measurableSet_singleton _)

theorem wholeFuture_rootSum_le_metricEntropy
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    ENNReal.ofReal (∑ p : ↥(allPositiveRoots (d+1) \ P),
      (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2) ≤
      measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let F := entireFutureObservation T Q
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hF : Measurable F := entireFutureObservation_measurable hT.measurable hQ
  have hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x := by
    filter_upwards [hversion] with x hx
    rw [hx]
    filter_upwards [c.ambientFutureMeasure_ae_same_names hP hf μ ell hell Q hQ 1 x]
      with y hy
    exact funext hy
  have hm : MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance ≤
      (inferInstance : MeasurableSpace (X (d+1))) := (κ.measurable.prodMk hF).comap_le
  have hfuture : (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y))) ≤ MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance := by
    rw [countableFutureSigma_eq_comap]
    exact (measurable_snd.comp (comap_measurable (fun x => (κ x,F x)))).comap_le
  have he := selfConstant_kernel_with_label_information μ κ F hF hstat hself hconst Q hQ
  have HI := c.wholeFuture_conditionalInformation_integrable_integral d hP hf μ hA
    ell hell Q hQ κ hstat hself hversion hmass
  have Hint : Integrable (conditionalInformation μ Q (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance)) μ := HI.1.congr he.symm
  have hprob (a : ℕ) :=
    (selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF hstat hself hconst
      (hQ (measurableSet_singleton a))).symm.trans
    (selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hQ (measurableSet_singleton a)))
  have hp := c.futureBlock_conditionalProbability d hP hf μ ell hell Q hQ κ
    hstat hself 1 hversion
  have hM := c.ae_all_futureMass_pos_ne_top d hP hf μ hA ell hell Q hQ hmass
  have hpos : ∀ᵐ x ∂μ, 0 < (μ[({z | Q z=Q x}.indicator
      (fun _ => (1 : ℝ))) | MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance]) x := by
    filter_upwards [ae_all_iff.mpr hprob,hp,hM] with x hx hp hM
    have hqx := hx (Q x)
    change (μ[({z | Q z=Q x}.indicator (fun _ => (1 : ℝ))) |
      MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance]) x =
        (μ[({z | Q z=Q x}.indicator (fun _ => (1 : ℝ))) |
          MeasurableSpace.comap κ inferInstance]) x at hqx
    rw [hqx]
    have ha : {y | orbitName T Q 1 y=orbitName T Q 1 x}={y | Q y=Q x} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        exact congrFun h 0
      · intro h
        funext i
        have hi : i=0 := Subsingleton.elim _ _
        subst i
        exact h
    change (μ[({y | orbitName T Q 1 y=orbitName T Q 1 x}.indicator
      (fun _ => (1 : ℝ))) | MeasurableSpace.comap κ inferInstance]) x = _ at hp
    rw [ha] at hp
    rw [hp,ENNReal.toReal_div]
    exact div_pos (ENNReal.toReal_pos (hM 0).1.ne' (hM 0).2)
      (ENNReal.toReal_pos (hM 1).1.ne' (hM 1).2)
  have H := conditionalInformation_integral_le_metricEntropy
    (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) μ hT Q hQ hm hfuture hpos Hint
  rwa [integral_congr_ae he,HI.2] at H

end EliminationChain
end DukePrimeDegree

end

end OAI
