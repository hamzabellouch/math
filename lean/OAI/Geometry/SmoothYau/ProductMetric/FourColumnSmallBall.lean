import Mathlib
import OAI.Geometry.SmoothYau.NodalMeasure.GaussianPDFStandardOne
import OAI.Geometry.SmoothYau.Smoothness.WaveJetMatrix

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology Matrix ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples
open MeasureTheory ProbabilityTheory

theorem four_column_smallBall {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (g : Ω → (Fin 2 ⊕ Fin 2 → ℝ)) (hg : Measurable g)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)
    (d : ℝ) (hd : 0 < d) (hA : d ≤ |A.det|)
    (r : ℝ) (hr : 0 ≤ r) :
    (ν.prod (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 1)))
      {w | Matrix.toLin' A w.2 + g w.1 ∈ Metric.closedBall 0 r} ≤
      ENNReal.ofReal d⁻¹ * (ENNReal.ofReal (2 * r)) ^ 4 := by
  have hApos : 0 < |A.det| := hd.trans_le hA
  have hdet : LinearMap.det (Matrix.toLin' A) ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact abs_pos.mp hApos
  calc
    _ ≤ ENNReal.ofReal (abs (LinearMap.det (Matrix.toLin' A))⁻¹) *
        (ENNReal.ofReal (2 * r)) ^ Fintype.card (Fin 2 ⊕ Fin 2) :=
      gaussian_independent_smallBall ν g hg 0 0 (Matrix.toLin' A) hdet r hr
    _ ≤ _ := by
      simp only [LinearMap.det_toLin', Fintype.card_sum, Fintype.card_fin]
      apply mul_le_mul_left
      apply ENNReal.ofReal_le_ofReal
      rw [abs_inv]
      exact inv_anti₀ hd hA

theorem column_scaled_det_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (c : ι → ℝ) (d q : ℝ)
    (hq : 0 ≤ q) (hdet : d ≤ |A.det|)
    (hc : ∀ i, q ≤ c i) :
    d * q ^ Fintype.card ι ≤ |(A * Matrix.diagonal c).det| := by
  rw [Matrix.det_mul, Matrix.det_diagonal, abs_mul]
  have hprod : q ^ Fintype.card ι ≤ ∏ i, c i := by
    calc
      _ = ∏ _i : ι, q := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hq) (fun index _ => hc index)
  have hpzero : 0 ≤ ∏ i, c i := Finset.prod_nonneg (fun i _ => hq.trans (hc i))
  rw [abs_of_nonneg hpzero]
  exact mul_le_mul hdet hprod (pow_nonneg hq _) (abs_nonneg _)

theorem wave_smallBall_uniform (M C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ A R : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ,
      ‖A‖ ≤ M → d * δ ≤ |A.det| → ‖R‖ ≤ C * δ ^ 2 →
      ∀ q : ℝ, 0 < q → ∀ c : Fin 2 ⊕ Fin 2 → ℝ, (∀ i, q ≤ c i) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (g : Ω → (Fin 2 ⊕ Fin 2 → ℝ)), Measurable g →
      ∀ r : ℝ, 0 ≤ r →
      (ν.prod (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 1)))
        {w | Matrix.toLin' ((A + R) * Matrix.diagonal c) w.2 + g w.1 ∈
          Metric.closedBall 0 r} ≤
        ENNReal.ofReal (d / 2 * δ * q ^ 4)⁻¹ * (ENNReal.ofReal (2 * r)) ^ 4 := by
  obtain ⟨ε, hε, he⟩ := determinant_uniform_error_bound (ι := Fin 2 ⊕ Fin 2) M C d hC hd
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε A R hA hdet hR q hq c hc Ω _ ν _ g hg r hr
  have hest := column_scaled_det_lower (A + R) c (d / 2 * δ) q
    hq.le (he δ hδ hδε A R hA hdet hR) hc
  norm_num only [Fintype.card_sum, Fintype.card_fin] at hest
  exact four_column_smallBall ν g hg ((A + R) * Matrix.diagonal c)
    (d / 2 * δ * q ^ 4) (by positivity) hest r hr

end YauCounterexamples


end

end OAI
