import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableAuxiliaryEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConullFiberEntropyOrder

namespace OAI

/-! # The auxiliary-future upper bound in terms of the actual kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma combined_future_kernel_entropy_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Measurable T)
    (Q R : Y → ℕ) (hQ : Measurable Q) (hR : Measurable R)
    (κ : Kernel Y Y) (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) → κ x=κ y)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B) :
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap
        (entireFutureObservation T (fun x => Encodable.encode (Q x,R x))) inferInstance) ≤
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (fun x => (κ x,entireFutureObservation T Q x)) inferInstance) := by
  have hQR : Measurable (fun x => Encodable.encode (Q x,R x)) :=
    (measurable_of_countable Encodable.encode).comp (hQ.prodMk hR)
  apply conditionalSigmaEntropy_le_of_conull_fibers μ
    (entireFutureObservation T (fun x => Encodable.encode (Q x,R x)))
    (entireFutureObservation_measurable hT hQR)
    (fun x => (κ x,entireFutureObservation T Q x))
    (κ.measurable.prodMk (entireFutureObservation_measurable hT hQ)) E hE _ B
    (fun b => hB (measurableSet_singleton b))
  intro x hx y hy hxy
  have hnames (k : ℕ) : Q (T^[k+1] x)=Q (T^[k+1] y) ∧
      R (T^[k+1] x)=R (T^[k+1] y) :=
    Prod.mk.inj (Encodable.encode_injective (congrFun hxy k))
  exact Prod.ext (hconst x hx y hy (fun k => (hnames k).1.symm)
    (fun k => (hnames k).2.symm)) (funext fun k => (hnames k).1)

theorem predecessor_auxiliary_kernel_entropyRate_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (R : Y → ℕ) (hR : Measurable R)
    (hfinite : Summable (fun n => Real.negMulLog (μ.real {x | R x=n})))
    (κ : Kernel Y Y) (E : Set Y) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (hconst : ∀ x ∈ E, ∀ y ∈ E,
      (∀ k : ℕ, Q (T^[k+1] y)=Q (T^[k+1] x)) →
      (∀ k : ℕ, R (T^[k+1] y)=R (T^[k+1] x)) → κ x=κ y)
    (K : ℕ) :
    observationEntropyRate μ T (heightClip Q K) ≤
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (fun x => (κ x,entireFutureObservation T Q x)) inferInstance) +
      ∑' n, Real.negMulLog (μ.real {x | R x=n}) := by
  exact (predecessor_countable_auxiliary_entropyRate_le μ hT Q hQ B hB href decode hdecode
    R hR hfinite K).trans (add_le_add
      (combined_future_kernel_entropy_le μ hT.measurable Q R hQ hR κ E hE hconst B hB)
      le_rfl)

end DukePrimeDegree

end

end OAI
