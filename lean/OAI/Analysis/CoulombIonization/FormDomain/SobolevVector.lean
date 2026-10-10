import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.Multiplier
import OAI.Analysis.CoulombIonization.Variational.Slices

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace CoulombAtom

def SobolevVector {N : ℕ} (ψ : FormVector N) : Prop :=
  (∀ s, MemLp (ψ.value s) 2) ∧
  (∀ s i a, MemLp (ψ.gradient s i a) 2) ∧
  (∀ s i a, IsWeakDerivative (direction i a) (ψ.value s) (ψ.gradient s i a))

lemma SobolevFermion.sobolevVector {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) : SobolevVector ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.1⟩

def multiplyForm {N : ℕ} (p : SmoothMultiplier (sectorDirections N))
    (ψ : FormVector N) : FormVector N where
  value s x := (p.value x : ℂ) * ψ.value s x
  gradient s i a x := (p.value x : ℂ) * ψ.gradient s i a x +
    Complex.ofReal (lineDeriv ℝ p.value x (direction i a)) * ψ.value s x

lemma SobolevVector.multiply {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (p : SmoothMultiplier (sectorDirections N)) : SobolevVector (multiplyForm p ψ) := by
  refine ⟨fun s => memLp_bounded_mul p.regular.continuous p.bound (hψ.1 s), ?_, ?_⟩
  · intro s i a
    exact (memLp_bounded_mul p.regular.continuous p.bound (hψ.2.1 s i a)).add
      (memLp_bounded_mul (p.derivative_continuous (i,a)) (p.gradient_bound (i,a)) (hψ.1 s))
  · intro s i a
    exact (hψ.2.2 s i a).mul_smooth (hψ.1 s) (hψ.2.1 s i a) p.regular

lemma SobolevFermion.multiply {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (p : FermionMultiplier N) : SobolevFermion (multiplyForm p.toSmoothMultiplier ψ) := by
  have hw := hψ.sobolevVector.multiply p.toSmoothMultiplier
  refine ⟨hw.1, hw.2.1, hw.2.2, ?_⟩
  intro π s
  filter_upwards [hψ.2.2.2 π s] with x hx
  change (p.value (x ∘ π) : ℂ) * ψ.value (s ∘ π) (x ∘ π) =
    _ * ((p.value x : ℂ) * ψ.value s x)
  rw [p.symmetric, hx]
  ring

lemma SobolevVector.nuclear_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i : Fin N) :
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i‖) :=
  CoulombAtom.nuclear_integrable i (hψ.1 s) (hψ.2.1 s i) (hψ.2.2 s i)

lemma SobolevVector.pair_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun x => ‖ψ.value s x‖ ^ 2 / ‖x i - x j‖) :=
  CoulombAtom.pair_integrable i j hij (hψ.1 s) (hψ.2.1 s i) (hψ.2.2 s i)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end

end OAI
