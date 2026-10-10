import Mathlib
import OAI.Computability.MinUncut.Estimates.Convolution
import OAI.Computability.MinUncut.Estimates.CoupledAnswer

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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def rowProjectedGradient (D : ℕ) (f : FoldedProof A) (σ η : ℝ)
    (B : FaceArray A m n) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  RowNoise.project D (fun C => gradient f C σ η c x) B

theorem gradient_row_tail (f : FoldedProof A) (hn : 0 < n)
    {σ a : ℝ} (hσ : σ≠0) (ha : 0≤a) (ha1 : a≤1) (η : ℝ) (D : ℕ)
    (hD : ∀ k : ℕ, D < k → 1≤(k:ℝ)*a) (c : Point m n → ℝ) :
    (𝔼 B : FaceArray A m n, spatialEnergy (fun x =>
      gradient f B σ η c x-rowProjectedGradient D f σ η B c x)) ≤
      4*σ⁻¹^2*(𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
        RowNoise.density a B C*secondRejection f B C σ η c) := by
  have htail (x : Point m n) := RowNoise.row_tail_le ha ha1 D hD
    (fun B : FaceArray A m n => gradient f B σ η c x)
  calc
    _ = ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n,
        𝔼 B : FaceArray A m n, (gradient f B σ η c x-rowProjectedGradient D f σ η B c x)^2 := by
      simp only [spatialEnergy,← Finset.mul_expect,Finset.expect_sum_comm]
    _ ≤ ((n^m:ℕ):ℝ)⁻¹*∑ x : Point m n,
        𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
          RowNoise.density a B C*(gradient f B σ η c x-gradient f C σ η c x)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => htail x)) (by positivity)
    _ = 𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
        RowNoise.density a B C*spatialEnergy
          (fun x => gradient f B σ η c x-gradient f C σ η c x) := by
      simp only [spatialEnergy,Finset.mul_sum,Finset.expect_sum_comm,
        ← Finset.mul_expect,mul_left_comm]
    _ ≤ 𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
        RowNoise.density a B C*(4*σ⁻¹^2*secondRejection f B C σ η c) :=
      Finset.expect_le_expect (fun B _ => Finset.expect_le_expect (fun C _ =>
        mul_le_mul_of_nonneg_left (gradient_second_comparison f B C hn hσ η c)
          (RowNoise.density_nonneg ha ha1 B C)))
    _ = _ := by
      have he (B C : FaceArray A m n) :
          RowNoise.density a B C*(4*σ⁻¹^2*secondRejection f B C σ η c) =
          (4*σ⁻¹^2)*(RowNoise.density a B C*secondRejection f B C σ η c) := by ring
      simp_rw [he,← Finset.mul_expect]
end MinUncut.Inner

end

end OAI
