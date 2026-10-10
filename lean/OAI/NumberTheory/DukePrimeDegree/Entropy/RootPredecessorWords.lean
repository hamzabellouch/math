import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPredecessorInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorWordEquivalence

namespace OAI

/-! # Exact finite-word root information in the ambient predecessor alphabet -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

private theorem labeled_kernel_information
    {Y S A : Type*} [MeasurableSpace Y] [MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    (μ : Measure Y) [IsFiniteMeasure μ] (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F) (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (Q : Y → A) (hQ : Measurable Q) :
    conditionalInformation μ Q
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =ᵐ[μ]
      conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) := by
  have h (a : A) :=
    (selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF hstat hself hconst
      (hQ (measurableSet_singleton a))).symm.trans
    (selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hQ (measurableSet_singleton a)))
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact congrArg (-Real.log ·) (hx (Q x))

namespace EliminationChain

theorem predecessor_word_root_information
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
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    {M : ℕ} (B : X (d+1) → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y →
      Q (rightAction x (diagonalOneParameter ell hell (-1)))=
        Q (rightAction y (diagonalOneParameter ell hell (-1))) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ)
    (hdecode : ∀ x,
      decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x)
    (N : ℕ) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let K := delayedFutureKernel κ (diagonalOneParameter ell hell (-1)) N
    let F := fullFutureObservation T Q (N+1)
    conditionalSigmaEntropy μ (orbitName T B (N+1))
      (MeasurableSpace.comap (fun x => (K x,F x)) inferInstance) =
      (N+1:ℝ)*∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let K := delayedFutureKernel κ (diagonalOneParameter ell hell (-1)) N
  let F := fullFutureObservation T Q (N+1)
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := fullFutureObservation_measurable hT hQ _
  have hK := delayedFutureKernel_spec d c hP hf μ hA ell hell Q κ hstat hself hversion N
  have hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂K x, F y=F x := by
    filter_upwards [hK.2.2] with x hx
    change K x=c.ambientFutureMeasure hP hf μ ell hell Q (N+1) x at hx
    rw [hx]
    filter_upwards [c.ambientFutureMeasure_ae_same_names hP hf μ ell hell Q hQ (N+1) x]
      with y hy
    funext k
    simpa only [F,fullFutureObservation,Nat.add_comm] using hy k
  have hQw : Measurable (orbitName T Q (N+1)) :=
    measurable_pi_iff.mpr fun i => hQ.comp (hT.iterate i.val)
  have hBw : Measurable (orbitName T B (N+1)) :=
    measurable_pi_iff.mpr fun i => hB.comp (hT.iterate i.val)
  have he := kernel_label_information_eq_of_fiber_equiv μ K F hF hK.1 hK.2.1 hconst
    (orbitName T Q (N+1)) hQw (orbitName T B (N+1)) hBw (by
      intro x y hxy
      apply predecessor_word_eq_iff T Q B href decode hdecode
      exact congrFun hxy 0)
  have hs := labeled_kernel_information μ K F hF hK.1 hK.2.1 hconst
    (orbitName T Q (N+1)) hQw
  have HI := delayedFuture_conditionalInformation_integrable_integral d c hP hf μ hA
    ell hell Q hQ κ hstat hself hversion hmass N
  have HB := conditionalInformation_fintype_integrable_integral
    (MeasurableSpace.comap (fun x => (K x,F x)) inferInstance) μ
    (orbitName T B (N+1)) hBw (K.measurable.prodMk hF).comap_le
  calc
    _ = ∫ x, conditionalInformation μ (orbitName T B (N+1))
        (MeasurableSpace.comap (fun x => (K x,F x)) inferInstance) x ∂μ := HB.2.symm
    _ = ∫ x, conditionalInformation μ (orbitName T Q (N+1))
        (MeasurableSpace.comap K inferInstance) x ∂μ :=
      integral_congr_ae (he.symm.trans hs)
    _ = _ := HI.2

end EliminationChain
end DukePrimeDegree

end

end OAI
