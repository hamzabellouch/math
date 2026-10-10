import Mathlib
import OAI.Computability.MinUncut.Estimates.Density
import OAI.Computability.MinUncut.Estimates.EuclideanInvariantScore

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
namespace MinUncut.Inner
open scoped BigOperators

variable {m n : ℕ}

def faceCorrelation (v : Point m n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun z : Code m n => |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)|)

lemma code_correlation_le (v : Point m n → ℝ) (z : Code m n) :
    |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)| ≤ faceCorrelation v := by
  exact Finset.le_sup' (fun w : Code m n => |𝔼 x : Point m n, v x * BinaryFourier.sign (w.val x)|) (Finset.mem_univ z)

lemma faceCorrelation_nonneg (v : Point m n → ℝ) : 0 ≤ faceCorrelation v :=
  (abs_nonneg _).trans (code_correlation_le v 0)

lemma faceCorrelation_le {v : Point m n → ℝ} {a : ℝ}
    (ha : ∀ z : Code m n, |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)| ≤ a) :
    faceCorrelation v ≤ a := Finset.sup'_le _ _ (fun z _ => ha z)

lemma faceCorrelation_le_l1 (v : Point m n → ℝ) :
    faceCorrelation v ≤ 𝔼 x : Point m n, |v x| := by
  apply faceCorrelation_le
  intro z
  calc
    _ ≤ 𝔼 x : Point m n, |v x * BinaryFourier.sign (z.val x)| :=
      Finset.abs_expect_le _ _
    _ = _ := by simp only [abs_mul, BinaryFourier.sign_abs, mul_one]

lemma faceCorrelation_add_le (v w : Point m n → ℝ) :
    faceCorrelation (v+w) ≤ faceCorrelation v + faceCorrelation w := by
  apply faceCorrelation_le
  intro z
  simp only [Pi.add_apply, add_mul, Finset.expect_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add (code_correlation_le v z) (code_correlation_le w z))

lemma faceCorrelation_neg (v : Point m n → ℝ) : faceCorrelation (-v) = faceCorrelation v := by
  unfold faceCorrelation
  simp only [Pi.neg_apply, neg_mul, Finset.expect_neg_distrib, abs_neg]

lemma faceCorrelation_lipschitz (v w : Point m n → ℝ) :
    |faceCorrelation v-faceCorrelation w| ≤ 𝔼 x : Point m n, |v x-w x| := by
  apply abs_le.mpr
  have h₁ := faceCorrelation_add_le (v-w) w
  have h₂ := faceCorrelation_add_le (w-v) v
  have h₃ := faceCorrelation_le_l1 (v-w)
  have h₄ := faceCorrelation_le_l1 (w-v)
  simp only [sub_add_cancel] at h₁ h₂
  simp only [Pi.sub_apply] at h₃ h₄
  simp_rw [abs_sub_comm (w _)] at h₄
  constructor <;> linarith

lemma representation_correlation (v : Point m n → ℝ) (μ : Code m n → ℝ) :
    |𝔼 x : Point m n, v x * (∑ z : Code m n, μ z * BinaryFourier.sign (z.val x))| ≤
      (∑ z : Code m n, |μ z|)*faceCorrelation v := by
  simp_rw [Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  calc
    _ ≤ ∑ z : Code m n, |𝔼 x : Point m n, v x * (μ z * BinaryFourier.sign (z.val x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z : Code m n, |μ z| * |𝔼 x : Point m n, v x * BinaryFourier.sign (z.val x)| := by
      apply Finset.sum_congr rfl
      intro z _
      simp_rw [mul_left_comm (v _), ← Finset.mul_expect]
      rw [abs_mul]
    _ ≤ ∑ z : Code m n, |μ z| * faceCorrelation v :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (code_correlation_le v z) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem gradient_convex_correlation (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ ≠ 0) (hη : η ≠ 0)
    (c : Point m n → ℝ) (v : Point m n → ℝ) :
    |𝔼 x : Point m n, v x * gradient f B σ η c x| ≤ tableMass f B σ η c * faceCorrelation v := by
  simp_rw [gradient_table_representation f B hn hσ hη]
  exact representation_correlation v (tableCoefficient f B σ η c)
end MinUncut.Inner

end

end OAI
