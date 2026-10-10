import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorEntropyLimit
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.BilateralFiniteCodes

namespace OAI

/-! # Countable future information controls full entropy

Finite predecessor symbols identify the integrable information of the
countable present given its entire future. Neutral bilateral fibers then
allow the bound to pass to every finite observation on the quotient.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem finite_predecessors_future_information_upper
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q) (hfinite : UniformFinitePredecessors T Q) :
    let F := entireFutureObservation T Q
    Integrable (conditionalInformation μ Q (MeasurableSpace.comap F inferInstance)) μ ∧
      ∀ L : ℕ, observationEntropyRate μ T (heightClip Q L) ≤
        ∫ x, conditionalInformation μ Q (MeasurableSpace.comap F inferInstance) x ∂μ := by
  let F := entireFutureObservation T Q
  have hF : Measurable F := entireFutureObservation_measurable hT.measurable hQ
  obtain ⟨M,B,decode,hB,href,hdecode,hupper⟩ :=
    finite_predecessors_entropy_upper μ hT Q hQ hfinite
  have hequiv : ∀ x y, F x=F y → (Q x=Q y ↔ B x=B y) := by
    intro x y hxy
    have ht : Q (T x)=Q (T y) := by
      simpa only [F,entireFutureObservation,Nat.zero_add,Function.iterate_one] using congrFun hxy 0
    constructor
    · intro h
      exact href x y h ht
    · intro h
      rw [←hdecode x,←hdecode y,ht,h]
  have he := conditionalInformation_eq_of_fiber_equiv μ F hF Q hQ B hB hequiv
  have hI := conditionalInformation_fintype_integrable_integral
    (MeasurableSpace.comap F inferInstance) μ B hB hF.comap_le
  refine ⟨hI.1.congr he.symm,?_⟩
  intro L
  rw [integral_congr_ae he,hI.2]
  exact hupper L

theorem diagonal_entropy_le_countable_future_information (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (hfinite : UniformFinitePredecessors
      (fun x => rightAction x (diagonalOneParameter ell hell (-1))) Q) :
    let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
    let F := entireFutureObservation T Q
    Integrable (conditionalInformation μ Q (MeasurableSpace.comap F inferInstance)) μ ∧
      measureEntropy μ T ≤ ENNReal.ofReal
        (∫ x, conditionalInformation μ Q (MeasurableSpace.comap F inferInstance) x ∂μ) := by
  let T := fun x => rightAction x (diagonalOneParameter ell hell (-1))
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  obtain ⟨hint,hupper⟩ := finite_predecessors_future_information_upper μ hT Q hQ hfinite
  exact ⟨hint,measureEntropy_le_of_bilateral_heightClip_bounds d ell hell Q hQ μ hA
    hlift _ hupper⟩

end DukePrimeDegree

end

end OAI
