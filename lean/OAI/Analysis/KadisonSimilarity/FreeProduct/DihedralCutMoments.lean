import OAI.Analysis.KadisonSimilarity.FreeProduct.AngularCutLimit
import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralArcProjection

namespace OAI

/-! Passing from the continuous Haar functional calculus to the actual
open spectral projection, using its bounded strong resolvent limit. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorTrace (Ω : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ H Ω)

omit [CompleteSpace H] in
@[simp] theorem vectorTrace_apply (Ω : H) (T : H →L[ℂ] H) :
    vectorTrace Ω T = inner ℂ Ω (T Ω) := rfl

theorem upperSpectralCut_vectorTrace_tendsto (Ω : H) (a b : H →L[ℂ] H) (c : ℝ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => vectorTrace Ω (supportResolvent (a - c • 1)⁺ (ε n) * b)) atTop
      (𝓝 (vectorTrace Ω (upperSpectralCut a c * b))) := by
  change Tendsto (fun n => inner ℂ Ω (supportResolvent (a - c • 1)⁺ (ε n) (b Ω)))
    atTop (𝓝 (inner ℂ Ω (rangeSupport (a - c • 1)⁺ (b Ω))))
  let B : H →L[ℂ] H := (a - c • 1)⁺
  have hB : 0 ≤ B := CFC.posPart_nonneg (a - c • 1)
  have ht := supportResolvent_tendsto B hB ε hε hlim (b Ω)
  exact ((innerSL ℂ Ω).continuous.tendsto (rangeSupport B (b Ω))).comp ht

private def regularizer (n : ℕ) : ℝ := (1 / 2) ^ n

private theorem regularizer_pos (n : ℕ) : 0 < regularizer n := by
  unfold regularizer
  positivity

private theorem regularizer_tendsto : Tendsto regularizer atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)

theorem dihedralArcProjection_rotation_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hhaar : ∀ l : ℤ, vectorTrace Ω (↑(w ^ l) : H →L[ℂ] H) = if l = 0 then 1 else 0)
    (θ : ℝ) (l : ℤ) :
    vectorTrace Ω (dihedralArcProjection (w : H →L[ℂ] H) θ * (↑(w ^ l) : H →L[ℂ] H)) =
      angularIntegral (fun x => if Real.cos θ < Real.cos x then 1 else 0) l := by
  have hleft := upperSpectralCut_vectorTrace_tendsto Ω (realPart (w : H →L[ℂ] H))
    (↑(w ^ l) : H →L[ℂ] H) (Real.cos θ) regularizer regularizer_pos regularizer_tendsto
  have heq (n : ℕ) :
      vectorTrace Ω (supportResolvent ((realPart (w : H →L[ℂ] H) : H →L[ℂ] H) -
          Real.cos θ • 1)⁺ (regularizer n) * (↑(w ^ l) : H →L[ℂ] H)) =
        angularIntegral (fun x => (spectralCutFunction (Real.cos θ) (regularizer n)
          (Real.cos x) : ℂ)) l := by
    rw [supportResolvent_positiveShift_eq_cfc _ (realPart (w : H →L[ℂ] H)).property
      _ (regularizer_pos n)]
    exact trace_cfc_realPart_rotation (vectorTrace Ω) w hw hwn hhaar _
      (spectralCutFunction_continuous _ (regularizer_pos n)) l
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft
    (angularIntegral_cut_tendsto (Real.cos θ) regularizer regularizer_pos regularizer_tendsto l)

theorem dihedralArcProjection_reflection_moment (Ω : H) (w : (H →L[ℂ] H)ˣ)
    (d : H →L[ℂ] H) (hw : star (w : H →L[ℂ] H) = (↑w⁻¹ : H →L[ℂ] H))
    (hwn : ‖(w : H →L[ℂ] H)‖ ≤ 1)
    (hcoset : ∀ l : ℤ, vectorTrace Ω ((↑(w ^ l) : H →L[ℂ] H) * d) = 0)
    (θ : ℝ) (l : ℤ) :
    vectorTrace Ω ((dihedralArcProjection (w : H →L[ℂ] H) θ *
      (↑(w ^ l) : H →L[ℂ] H)) * d) = 0 := by
  have hleft := upperSpectralCut_vectorTrace_tendsto Ω (realPart (w : H →L[ℂ] H))
    ((↑(w ^ l) : H →L[ℂ] H) * d) (Real.cos θ) regularizer regularizer_pos regularizer_tendsto
  have heq (n : ℕ) : vectorTrace Ω
      (supportResolvent ((realPart (w : H →L[ℂ] H) : H →L[ℂ] H) - Real.cos θ • 1)⁺
        (regularizer n) * ((↑(w ^ l) : H →L[ℂ] H) * d)) = 0 := by
    rw [supportResolvent_positiveShift_eq_cfc _ (realPart (w : H →L[ℂ] H)).property
      _ (regularizer_pos n)]
    simpa only [mul_assoc] using trace_cfc_realPart_rotation_reflection
      (vectorTrace Ω) w d hw hwn hcoset _
      (spectralCutFunction_continuous _ (regularizer_pos n)).continuousOn l
  simp only [heq] at hleft
  have hzero : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
  simpa only [dihedralArcProjection, upperSpectralCut, mul_assoc] using
    tendsto_nhds_unique hleft hzero

end KadisonSimilarity

end

end OAI
