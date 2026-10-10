import OAI.Geometry.Relativity.CKS.CKSMetricPositivity
import OAI.Geometry.Relativity.CKS.ConeSupport
import OAI.Geometry.Relativity.CKS.AreaGram

namespace OAI

noncomputable section
namespace CKSArea
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal
abbrev AmbientMat := Matrix (Fin 3) (Fin 3) ℝ
abbrev TangentFrame := Matrix (Fin 3) (Fin 2) ℝ

def gram (g : AmbientMat) (T : TangentFrame) : Mat2 := Tᴴ*g*T

lemma gram_posDef {g : AmbientMat} (hg : g.PosDef) {T : TangentFrame}
    (hT : Function.Injective T.mulVec) : (gram g T).PosDef :=
  hg.conjTranspose_mul_mul_same hT

lemma gram_difference (g p : AmbientMat) (T : TangentFrame) (c : ℝ) :
    gram p T-c • gram g T=gram (p-c • g) T := by
  simp only [gram,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]

lemma gram_density_lower {g p : AmbientMat} {T : TangentFrame} {c : ℝ}
    (hg : g.PosDef) (hT : Function.Injective T.mulVec) (hc : 0 ≤ c)
    (h : (p-c • g).PosSemidef) : c*density (gram g T) ≤ density (gram p T) := by
  apply density_lower_bound (gram_posDef hg hT) hc
  rw [gram_difference]
  exact h.conjTranspose_mul_mul_same T

variable {α : Type*} [MeasurableSpace α]

def chartArea (g : α → AmbientMat) (T : α → TangentFrame) (μ : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (density (gram (g x) (T x))) ∂μ

theorem chartArea_lower {g p : α → AmbientMat} {T : α → TangentFrame} {c : ℝ}
    (μ : Measure α) (hg : ∀ x, (g x).PosDef) (hT : ∀ x, Function.Injective (T x).mulVec)
    (hc : 0 ≤ c) (h : ∀ x, (p x-c • g x).PosSemidef) :
    ENNReal.ofReal c*chartArea g T μ ≤ chartArea p T μ := by
  unfold chartArea
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono; intro x
  dsimp only
  rw [← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (gram_density_lower (hg x) (hT x) hc (h x))

theorem full_infimum_lower {Cut : Type*} (a b : Cut → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ s, c*a s ≤ b s) : c*(⨅ s, a s) ≤ ⨅ s, b s := by
  apply le_iInf; intro s
  calc c*(⨅ t, a t) ≤ c*a s := by gcongr; exact iInf_le a s
       _ ≤ b s := h s

theorem full_chart_infimum_lower {Cut : Type*} {g p : Cut → α → AmbientMat}
    {T : Cut → α → TangentFrame} (μ : Cut → Measure α) {c : ℝ}
    (hg : ∀ s x, (g s x).PosDef) (hT : ∀ s x, Function.Injective (T s x).mulVec)
    (hc : 0 ≤ c) (h : ∀ s x, (p s x-c • g s x).PosSemidef) :
    ENNReal.ofReal c*(⨅ s, chartArea (g s) (T s) (μ s)) ≤
      ⨅ s, chartArea (p s) (T s) (μ s) :=
  full_infimum_lower _ _ _ (fun s => chartArea_lower (μ s) (hg s) (hT s) hc (h s))

theorem real_full_chart_infimum_lower {Cut : Type*} {g p : Cut → α → AmbientMat}
    {T : Cut → α → TangentFrame} (μ : Cut → Measure α) {c : ℝ}
    (hg : ∀ s x, (g s x).PosDef) (hT : ∀ s x, Function.Injective (T s x).mulVec)
    (hc : 0 ≤ c) (h : ∀ s x, (p s x-c • g s x).PosSemidef)
    (finite : ⨅ s, chartArea (p s) (T s) (μ s) ≠ ∞) :
    c*(⨅ s, chartArea (g s) (T s) (μ s)).toReal ≤
      (⨅ s, chartArea (p s) (T s) (μ s)).toReal := by
  have hh := ENNReal.toReal_mono finite (full_chart_infimum_lower μ hg hT hc h)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using hh

end
end CKSArea

end

end OAI
