import Mathlib
import OAI.Geometry.SmoothYau.Estimates.ComplexGaussianRealValue

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

def complexRealResponse {ι : Type*} (J : Fin 3 → ι → ℂ) (γ : Fin 3 → ℂ) : ι → ℝ :=
  fun i => ∑ ℓ, (γ ℓ*J ℓ i).re

lemma complexRealResponse_selected (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (v : (Fin 2 → ℝ) × ((Fin 1 ⊕ Fin 3) → ℝ)) :
    complexRealResponse J (selectedComplexCoefficients v) =
      Matrix.toLin' (selectedComplexJetMatrix J) v.2 +
        (fun i => v.1 0*(J 1 i).re+v.1 1*(J 2 i).im) := by
  ext i
  simp [complexRealResponse,selectedComplexCoefficients,selectedComplexJetMatrix,
    Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_succ,
    Complex.mul_re,Complex.mul_im]
  ring

lemma measurable_complexRealResponse {ι : Type*} (J : Fin 3 → ι → ℂ) :
    Measurable (complexRealResponse J) := by
  unfold complexRealResponse
  fun_prop

theorem complex_three_wave_smallBall {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)) (hn : Measurable noise)
    (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (d : ℝ) (hd : 0 < d) (hdet : d ≤ |(selectedComplexJetMatrix J).det|)
    (r : ℝ) (hr : 0 ≤ r) :
    (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {v | complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} ≤
      ENNReal.ofReal d⁻¹*(ENNReal.ofReal (2*r))^4 := by
  let μ2 := Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)
  let μ4 := Measure.pi (fun _ : Fin 1 ⊕ Fin 3 => gaussianReal 0 1)
  let extra : Ω × (Fin 2 → ℝ) → ((Fin 1 ⊕ Fin 3) → ℝ) :=
    fun v i => v.2 0*(J 1 i).re+v.2 1*(J 2 i).im+noise v.1 i
  have he : Measurable extra := by unfold extra; fun_prop
  have hne : LinearMap.det (Matrix.toLin' (selectedComplexJetMatrix J)) ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact abs_pos.mp (hd.trans_le hdet)
  have hb := gaussian_independent_smallBall (μ.prod μ2) extra he (fun _ => 0) 0
    (Matrix.toLin' (selectedComplexJetMatrix J)) hne r hr
  norm_num only [Fintype.card_sum,Fintype.card_fin] at hb
  have hpr := ((MeasurePreserving.id μ).prod selectedComplexCoefficients_law).comp
    (measurePreserving_prodAssoc μ μ2 μ4)
  have hs : MeasurableSet {v : Ω × (Fin 3 → ℂ) |
      complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} :=
    ((measurable_complexRealResponse J).comp measurable_snd |>.add
        (hn.comp measurable_fst)) Metric.isClosed_closedBall.measurableSet
  have hp := hpr.measure_preimage hs.nullMeasurableSet
  rw [←hp]
  have hset : (Prod.map id selectedComplexCoefficients ∘ ⇑MeasurableEquiv.prodAssoc) ⁻¹'
      {v | complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} =
      {v : (Ω × (Fin 2 → ℝ)) × ((Fin 1 ⊕ Fin 3) → ℝ) |
        Matrix.toLin' (selectedComplexJetMatrix J) v.2+extra v.1 ∈ Metric.closedBall 0 r} := by
    ext v
    change complexRealResponse J (selectedComplexCoefficients (v.1.2,v.2))+noise v.1.1 ∈ Metric.closedBall 0 r ↔
      Matrix.toLin' (selectedComplexJetMatrix J) v.2+extra v.1 ∈ Metric.closedBall 0 r
    rw [complexRealResponse_selected]
    have hv : (Matrix.toLin' (selectedComplexJetMatrix J) v.2 +
        (fun i => v.1.2 0*(J 1 i).re+v.1.2 1*(J 2 i).im))+noise v.1.1 =
        Matrix.toLin' (selectedComplexJetMatrix J) v.2+extra v.1 := by
      ext i
      simp [extra,add_assoc]
    change (_+_)+noise v.1.1 ∈ Metric.closedBall 0 r ↔ _+_ ∈ Metric.closedBall 0 r
    rw [hv]
  rw [hset]
  apply hb.trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  rw [LinearMap.det_toLin',abs_inv]
  exact inv_anti₀ hd hdet

lemma complexRealResponse_rotation (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (e : Fin 3 → Circle) (γ : Fin 3 → ℂ) :
    complexRealResponse (fun ℓ i => (e ℓ : ℂ)*J ℓ i) γ =
      complexRealResponse J (fun ℓ => (e ℓ : ℂ)*γ ℓ) := by
  ext i
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 1
  ring

theorem complex_three_wave_rotated_smallBall {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)) (hn : Measurable noise)
    (J : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ) (e : Fin 3 → Circle)
    (d : ℝ) (hd : 0 < d) (hdet : d ≤ |(selectedComplexJetMatrix J).det|)
    (r : ℝ) (hr : 0 ≤ r) :
    (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
      {v | complexRealResponse (fun ℓ i => (e ℓ : ℂ)*J ℓ i) v.2+noise v.1 ∈ Metric.closedBall 0 r} ≤
      ENNReal.ofReal d⁻¹*(ENNReal.ofReal (2*r))^4 := by
  have hp := (MeasurePreserving.id μ).prod (gaussian_complex_pi_rotation e)
  have hs : MeasurableSet {v : Ω × (Fin 3 → ℂ) |
      complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} :=
    ((measurable_complexRealResponse J).comp measurable_snd |>.add
        (hn.comp measurable_fst)) Metric.isClosed_closedBall.measurableSet
  have hm := hp.measure_preimage hs.nullMeasurableSet
  have heq : {v : Ω × (Fin 3 → ℂ) |
      complexRealResponse (fun ℓ i => (e ℓ : ℂ)*J ℓ i) v.2+noise v.1 ∈ Metric.closedBall 0 r} =
      (Prod.map id (fun γ ℓ => (e ℓ : ℂ)*γ ℓ)) ⁻¹'
      {v | complexRealResponse J v.2+noise v.1 ∈ Metric.closedBall 0 r} := by
    ext v
    simp [complexRealResponse_rotation]
  rw [heq,hm]
  exact complex_three_wave_smallBall μ noise hn J d hd hdet r hr

end YauCounterexamples
end

end OAI
