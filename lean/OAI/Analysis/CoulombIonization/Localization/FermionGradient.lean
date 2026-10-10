import Mathlib
import OAI.Analysis.CoulombIonization.Localization.FermionL2
import OAI.Analysis.CoulombIonization.Localization.PacketFourier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open MeasureTheory Filter
open scoped ENNReal
namespace CoulombPackets
open CoulombPauli
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def HasFermionGradient {N : ℕ} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (ψ : fermionL2 (V := V) (N+1))
    (u : Fin (N+1) → ι → fermionL2 (V := V) (N+1)) : Prop :=
  ∀ i a, HasWeakSpinPartialDerivative (splitFermion i ψ) (splitFermion i (u i a)) (b a)

end CoulombPackets

end

end OAI
