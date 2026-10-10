import Mathlib
import OAI.Computability.MinUncut.Estimates.CollisionIndicator
import OAI.Computability.MinUncut.Graphs.VertexInjective

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
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

def pointField (V : Point m n → ℝ → ℝ) (c : Point m n → ℝ) (x : Point m n) : ℝ := V x (c x)

lemma pointField_continuous (V : Point m n → ℝ → ℝ) (hV : ∀ x, Continuous (V x)) (x : Point m n) :
    Continuous (fun c => pointField V c x) := (hV x).comp (continuous_apply x)

lemma point_correlation_continuous (V : Point m n → ℝ → ℝ) (hV : ∀ x, Continuous (V x)) :
    Continuous (fun c => faceCorrelation (pointField V c)) := by
  unfold faceCorrelation
  apply Continuous.finset_sup'_apply
  intro z _
  apply Continuous.abs
  simp only [Finset.expect_eq_sum_div_card]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro x _
  exact (pointField_continuous V hV x).mul continuous_const

lemma point_cube_abs (V : Point m n → ℝ → ℝ) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) (x y : Point m n) (c : Point m n → ℝ) :
    |∏ ν : Fin m → Bool, pointField V c (Box.vertex ν x y)|≤C^(2^m) := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ ν : Fin m → Bool, |C| := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      (fun _ _ => (hV _ _).trans (le_abs_self C))
    _ = _ := by simp [abs_of_nonneg hC]

lemma point_cube_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : Point m n → ℝ → ℝ) (hcont : ∀ x, Continuous (V x)) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) (x y : Point m n) :
    Integrable (fun c => ∏ ν : Fin m → Bool, pointField V c (Box.vertex ν x y)) (Measure.pi (fun _ : Point m n => μ)) := by
  apply Box.bounded_integrable
  · exact (continuous_finsetProd _ (fun _ _ => pointField_continuous V hcont _)).aestronglyMeasurable
  · exact point_cube_abs V hC hV x y

lemma point_moment_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : Point m n → ℝ → ℝ) (hcont : ∀ x, Continuous (V x)) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) :
    (∫ c, Box.moment (pointField V c) ∂Measure.pi (fun _ : Point m n => μ)) =
      𝔼 x : Point m n, 𝔼 y : Point m n, ∫ c, ∏ ν : Fin m → Bool,
        pointField V c (Box.vertex ν x y) ∂Measure.pi (fun _ : Point m n => μ) := by
  unfold Box.moment
  rw [Box.integral_expect _ (fun x => ?_)]
  · apply Finset.expect_congr rfl
    intro x _
    exact Box.integral_expect _ (fun y => point_cube_integrable μ V hcont hC hV x y)
  · simp only [Finset.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun y _ => point_cube_integrable μ V hcont hC hV x y)).div_const _

lemma centered_point_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : Point m n → ℝ → ℝ) (hcont : ∀ x, Continuous (V x)) {C : ℝ} (hC : 0≤C)
    (hV : ∀ x t, |V x t|≤C) (hmean : ∀ x, (∫ t, V x t ∂μ)=0) (hn : 0 < n) :
    (∫ c, Box.moment (pointField V c) ∂Measure.pi (fun _ : Point m n => μ)) ≤ C^(2^m)*((m:ℝ)/n) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [point_moment_integral μ V hcont hC hV]
  have hb (x y : Point m n) :
      (∫ c, ∏ ν : Fin m → Bool, pointField V c (Box.vertex ν x y) ∂Measure.pi (fun _ : Point m n => μ)) ≤
        C^(2^m)*(if ∃ i, x i=y i then (1:ℝ) else 0) := by
    by_cases hxy : ∃ i, x i=y i
    · simp only [ite_eq_left hxy,mul_one]
      calc
        _ ≤ ∫ _c : Point m n → ℝ, C^(2^m) ∂Measure.pi (fun _ : Point m n => μ) :=
          integral_mono (point_cube_integrable μ V hcont hC hV x y) (integrable_const _)
            (fun c => (le_abs_self _).trans (point_cube_abs V hC hV x y c))
        _ = _ := by simp
    · have hz := CubeRows.centered_point_cube_zero μ V (fun x => (hcont x).measurable) hmean x y
        (by simpa only [not_exists] using hxy)
      change _=0 at hz
      rw [show (∫ c, ∏ ν : Fin m → Bool, pointField V c (Box.vertex ν x y) ∂Measure.pi (fun _ : Point m n => μ))=0 from hz]
      simp only [ite_eq_right hxy,mul_zero,le_refl]
  calc
    _ ≤ 𝔼 x : Point m n, 𝔼 y : Point m n, C^(2^m)*(if ∃ i, x i=y i then (1:ℝ) else 0) :=
      Finset.expect_le_expect (fun x _ => Finset.expect_le_expect (fun y _ => hb x y))
    _ = C^(2^m)*(𝔼 x : Point m n, 𝔼 y : Point m n, if ∃ i, x i=y i then (1:ℝ) else 0) := by
      simp only [← Finset.mul_expect]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
      have collisionBound := CubeRows.collision_probability (ι := Fin m) (A := Fin n)
      simp only [Fintype.card_fin] at collisionBound
      convert collisionBound using 1
      congr 1
      funext point
      apply Finset.expect_congr rfl
      intro other _
      by_cases collision : ∃ index, point index = other index <;> simp [collision]
end MinUncut.Inner

end

end OAI
