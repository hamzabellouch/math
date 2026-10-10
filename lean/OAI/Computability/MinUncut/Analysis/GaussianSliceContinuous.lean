import Mathlib
import OAI.Computability.MinUncut.Analysis.SelectedProjectGaussianLocal
import OAI.Computability.MinUncut.Analysis.CenteredPointCorrelationPower
import OAI.Computability.MinUncut.Estimates.SelectedProjectSliceContinuous

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

lemma gaussianSlice_continuous (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) :
    Continuous (gaussianSlice f σ η x Y J B C) :=
  selectedProject_slice_continuous _ _ _ _ _

theorem processed_zero_correlation_power (f : FoldedProof A) (σ η : ℝ)
    (hm : 0 < m) (hn : 0 < n) {k : ℕ} (Y : ∀ x : Point m n, Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (C : Point m n → ℝ) {A₀ : ℝ} (hA : 0≤A₀) :
    (∫ c, faceCorrelation (pointField (fun x => Slice.centeredClip γ A₀
      (gaussianSlice f σ η x (Y x) J B C)) c) ∂γpi (Point m n))^(2^m) ≤
        (2*A₀)^(2^m)*((m:ℝ)/n) := by
  apply centered_point_correlation_power γ _
    (fun x => Slice.centeredClip_continuous γ A₀ _ (gaussianSlice_continuous f σ η x (Y x) J B C))
    (by positivity)
    (fun x t => Slice.centeredClip_abs_le hA (gaussianSlice_memLp f σ η x (Y x) J B C) t)
    (fun x => Slice.centeredClip_mean_zero hA (gaussianSlice_memLp f σ η x (Y x) J B C)) hm hn

lemma processed_zero_slice_loss (f : FoldedProof A) (σ η : ℝ) (x : Point m n)
    {k : ℕ} (Y : Subbox.PointedBox x k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (hJ : ∀ j ∈ J, j.1.card < (m-(∑ u, j.2 u)).choose 2)
    (B : FaceArray A m n) (C : Point m n → ℝ) {A₀ : ℝ} (hA : 0 < A₀) :
    (∫ t, |gaussianSlice f σ η x Y J B C t-
      Slice.centeredClip γ A₀ (gaussianSlice f σ η x Y J B C) t| ∂γ) ≤
        2*(∫ t, (gaussianSlice f σ η x Y J B C t)^2 ∂γ)/A₀ := by
  exact Slice.centeredClip_loss hA (gaussianSlice_memLp f σ η x Y J B C)
    (gaussianSlice_mean f σ η x Y J hJ B C)
end MinUncut.Inner

end

end OAI
