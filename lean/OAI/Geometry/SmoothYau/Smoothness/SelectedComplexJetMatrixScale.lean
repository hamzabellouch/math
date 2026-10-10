import Mathlib
import OAI.Geometry.SmoothYau.SphereMetric.ComplexRealResponse

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
open Set MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Topology Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma selectedComplexJetMatrix_scale (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) (w : Fin 3 → ℝ) :
    selectedComplexJetMatrix (fun ℓ i => (w ℓ : ℂ)*J ℓ i) =
      selectedComplexJetMatrix J * Matrix.diagonal
        (Sum.elim (fun _ : Fin 1 => w 0) (fun k : Fin 3 => ![w 2,w 0,w 1] k)) := by
  ext i j
  rcases j with j|j
  · simp [selectedComplexJetMatrix,Matrix.mul_diagonal,Complex.mul_re,mul_comm]
  · fin_cases j <;> simp [selectedComplexJetMatrix,Matrix.mul_diagonal,Complex.mul_re,Complex.mul_im,mul_comm]

theorem physical_complex_wave_smallBall_uniform (M C η : ℝ) (hM : 1 ≤ M)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ a ν b c : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      ∀ J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ,
        ‖selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ‖ ≤ C*δ^2 →
      ∀ q : ℝ, 0 < q → ∀ w : Fin 3 → ℝ, (∀ i, q ≤ w i) → ∀ e : Fin 3 → Circle,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ i => (e ℓ : ℂ)*((w ℓ : ℂ)*J ℓ i)) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*q^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  have hd : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  obtain ⟨ε,hε,he⟩ := determinant_uniform_error_bound (ι := Fin 1 ⊕ Fin 3) (M+1) C (Real.sqrt η) hC hd
  refine ⟨min ε 1,lt_min hε zero_lt_one,?_⟩
  intro δ hδ hδε a ν b c ha hν hb hc hbn hcn hbM hcM hang J hJ q hq w hw e Ω _ μ _ noise hn r hr
  have hδ1 : δ ≤ 1 := (hδε.trans_le (min_le_right _ _)).le
  have hdet : Real.sqrt η/2*δ ≤ |(selectedComplexJetMatrix J).det| := by
    have h := he δ hδ (hδε.trans_le (min_le_left _ _)) _
      (selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ)
      (physicalWaveJetMatrix_bound a ν b c δ M hM ha hν hbM hcM hδ.le hδ1)
      (physicalWaveJetMatrix_det_lower a ν b c δ η hν hb hc hbn hcn hη hang hδ.le) hJ
    simpa only [add_sub_cancel] using h
  let w' := Sum.elim (fun _ : Fin 1 => w 0) (fun k : Fin 3 => ![w 2,w 0,w 1] k)
  have hw' : ∀ i, q ≤ w' i := by
    rintro (i|i)
    · exact hw 0
    · fin_cases i
      · exact hw 2
      · exact hw 0
      · exact hw 1
  have hbnd := column_scaled_det_lower (selectedComplexJetMatrix J) w'
    (Real.sqrt η/2*δ) q hq.le hdet hw'
  norm_num only [Fintype.card_sum,Fintype.card_fin] at hbnd
  have hsc : Real.sqrt η/2*δ*q^4 ≤
      |(selectedComplexJetMatrix (fun ℓ i => (w ℓ : ℂ)*J ℓ i)).det| := by
    rw [selectedComplexJetMatrix_scale]
    exact hbnd
  exact complex_three_wave_rotated_smallBall μ noise hn _ e _ (by positivity) hsc r hr

end YauCounterexamples
end

end OAI
