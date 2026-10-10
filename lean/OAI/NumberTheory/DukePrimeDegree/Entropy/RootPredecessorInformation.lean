import OAI.NumberTheory.DukePrimeDegree.Entropy.KernelFutureInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorInformation

namespace OAI

/-! # Finite predecessor information on actual root future fibers -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
/-- Recoding on a stationary kernel fiber does not require measurable
 equality on its measure-valued label. -/
theorem kernel_label_information_eq_of_fiber_equiv
    {Y S α β : Type*} [MeasurableSpace Y] [MeasurableSpace S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (μ : Measure Y) [IsFiniteMeasure μ] (κ : Kernel Y Y) [IsMarkovKernel κ]
    (F : Y → S) (hF : Measurable F) (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (hequiv : ∀ x y, F x=F y → (P x=P y ↔ B x=B y)) :
    conditionalInformation μ P
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =ᵐ[μ]
      conditionalInformation μ B
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) := by
  have hp (a : α) : (fun x => (κ x).real {y | P y=a}) =ᵐ[μ]
      μ[({y | P y=a}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] :=
    selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF
      hstat hself hconst (hP (measurableSet_singleton a))
  have hb (b : β) : (fun x => (κ x).real {y | B y=b}) =ᵐ[μ]
      μ[({y | B y=b}.indicator (fun _ => (1:ℝ))) |
        MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance] :=
    selfConstant_kernel_with_label_ae_eq_condExp μ κ F hF
      hstat hself hconst (hB (measurableSet_singleton b))
  filter_upwards [ae_all_iff.mpr hp,ae_all_iff.mpr hb,hconst] with x hxP hxB hxF
  unfold conditionalInformation
  rw [←hxP (P x),←hxB (B x)]
  have hm : κ x {y | P y=P x}=κ x {y | B y=B x} := by
    apply measure_congr
    filter_upwards [hxF] with y hy
    exact propext (hequiv y x hy)
  rw [show (κ x).real {y | P y=P x}=(κ x).real {y | B y=B x} from
    congrArg ENNReal.toReal hm]

namespace EliminationChain

/-- The same finite predecessor symbol used for the ambient entropy
bound has exactly the root-information integral on the finer root fibers. -/
theorem predecessor_root_information
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
      decode (Q (rightAction x (diagonalOneParameter ell hell (-1)))) (B x)=Q x) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := entireFutureObservation T Q
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) =
      ∑ p : ↥(allPositiveRoots (d+1) \ P),
        (ell p.val.2-ell p.val.1)*canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  let F := entireFutureObservation T Q
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hF : Measurable F := entireFutureObservation_measurable hT hQ
  have hconst : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, F y=F x := by
    filter_upwards [hversion] with x hx
    rw [hx]
    filter_upwards [c.ambientFutureMeasure_ae_same_names hP hf μ ell hell Q hQ 1 x]
      with y hy
    exact funext hy
  have he := kernel_label_information_eq_of_fiber_equiv μ κ F hF hstat hself hconst
    Q hQ B hB (by
      intro x y hxy
      have ht : Q (T x)=Q (T y) := by
        simpa only [F,entireFutureObservation,Nat.zero_add,Function.iterate_one] using
          congrFun hxy 0
      exact ⟨fun h => href x y h ht,fun hb => by rw [←hdecode x,←hdecode y,ht,hb]⟩)
  have hs := selfConstant_kernel_with_label_information μ κ F hF hstat hself hconst Q hQ
  have HI := c.wholeFuture_conditionalInformation_integrable_integral d hP hf μ hA
    ell hell Q hQ κ hstat hself hversion hmass
  have HB := conditionalInformation_fintype_integrable_integral
    (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) μ B hB
    (κ.measurable.prodMk hF).comap_le
  calc
    _ = ∫ x, conditionalInformation μ B
        (MeasurableSpace.comap (fun x => (κ x,F x)) inferInstance) x ∂μ := HB.2.symm
    _ = ∫ x, conditionalInformation μ Q
        (MeasurableSpace.comap κ inferInstance) x ∂μ :=
      integral_congr_ae (he.symm.trans hs)
    _ = _ := HI.2

end EliminationChain
end DukePrimeDegree

end

end OAI
