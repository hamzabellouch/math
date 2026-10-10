import Mathlib
import OAI.Computability.MinUncut.Estimates.PointField

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
variable {m n : ℕ}

theorem centered_point_correlation_power (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : Point m n → ℝ → ℝ) (hcont : ∀ x, Continuous (V x)) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) (hmean : ∀ x, (∫ t, V x t ∂μ)=0)
    (hm : 0 < m) (hn : 0 < n) :
    (∫ c, faceCorrelation (pointField V c) ∂Measure.pi (fun _ : Point m n => μ))^(2^m) ≤
      C^(2^m)*((m:ℝ)/n) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hb (c : Point m n → ℝ) : |faceCorrelation (pointField V c)|≤C := by
    rw [abs_of_nonneg (faceCorrelation_nonneg _)]
    exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun x _ => hV x (c x))).trans_eq (Fintype.expect_const C))
  have hi : Integrable (fun c => faceCorrelation (pointField V c)^(2^m)) (Measure.pi (fun _ : Point m n => μ)) := by
    apply Box.bounded_integrable (C := C^(2^m)) ((point_correlation_continuous V hcont).pow _).aestronglyMeasurable
    intro c
    simp only [Pi.pow_apply, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb c) _
  have hmom : Integrable (fun c => Box.moment (pointField V c)) (Measure.pi (fun _ : Point m n => μ)) := by
    unfold Box.moment
    simp only [Finset.expect_eq_sum_div_card]
    apply Integrable.div_const
    apply integrable_finsetSum
    intro x _
    apply Integrable.div_const
    exact integrable_finsetSum _ (fun y _ => point_cube_integrable μ V hcont hC hV x y)
  calc
    _ ≤ ∫ c, faceCorrelation (pointField V c)^(2^m) ∂Measure.pi (fun _ : Point m n => μ) :=
      Box.integral_pow_bound (point_correlation_continuous V hcont).aestronglyMeasurable hb
        (fun c => faceCorrelation_nonneg _) _
    _ ≤ ∫ c, Box.moment (pointField V c) ∂Measure.pi (fun _ : Point m n => μ) :=
      integral_mono hi hmom (fun c => faceCorrelation_box_cs hm hn _)
    _ ≤ _ := centered_point_moment μ V hcont hC hV hmean hn
end MinUncut.Inner
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

lemma pairSlice_odd (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (c : Point m n → ℝ) (b : Forms A) :
    pairSlice f σ η x Y p J B c (b+AffineMap.const F₂ A 1) =
      -pairSlice f σ η x Y p J B c b := by
  apply localSlice_odd
  intro j hj α hm hc
  exact (joint_pair_matching f hσ η x j.2 j.1 p
    (retained_pair_admissible x Y p J j hj) α hm hc).2

lemma pairSlice_coefficient_zero (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (x : Point m n) {k : ℕ} (Y : Subbox.PointedBox x k) (p : PairClass m)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (c : Point m n → ℝ) (α : Module.Dual F₂ (Forms A))
    (ha : α (AffineMap.const F₂ A 1)≠1) : coefficient (pairSlice f σ η x Y p J B c) α=0 :=
  odd_coefficient_zero _ _ (pairSlice_odd f hσ η x Y p J B c) α ha

theorem processed_pair_correlation_power (f : FoldedProof A) {σ : ℝ} (hσ : σ≠0) (η : ℝ)
    (hm : 0 < m) (hn : 0 < n) {k : ℕ} (Y : ∀ x : Point m n, Subbox.PointedBox x k)
    (p : PairClass m) (J : Finset (Finset (Row m n) × (Point m n → ℕ)))
    (B : FaceArray A m n) (c : Point m n → ℝ) {H γ A₀ : ℝ} (hA : 0 < A₀) (hγ : 0≤γ) :
    (𝔼 Bj, 𝔼 Bi, faceCorrelation (pairField p.val.1 p.val.2
      (fun x => Slice.processed H γ A₀ (AffineMap.const F₂ A 1) (pairSlice f σ η x (Y x) p J B c)) Bj Bi))^(2^m) ≤
      A₀^(2^m)*((m:ℝ)/n) + ((γ+H^2/A₀)^2*H^2)^(2^Fintype.card (CubeRows.Other p.val.1 p.val.2)) := by
  apply pair_correlation_power hm hn _ _ (ne_of_lt p.property) _ (γ+H^2/A₀) H A₀
    (by positivity) hA.le
  · intro x α
    exact Slice.processed_coefficient_le hA hγ _ _ (pairSlice_coefficient_zero f hσ η x (Y x) p J B c) α
  · intro x
    exact Slice.processed_energy_le hA.le _ _
  · intro x b
    exact Slice.processed_abs_le hA.le _ _ b
end MinUncut.Inner

end

end OAI
