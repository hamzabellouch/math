import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiInvariantFrame
import OAI.Geometry.TamingCompatibility.Hodge.LocalCodifferential

namespace OAI


noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)

include hb h0 h1 h2 h3 hF in
omit [FiniteDimensional ℝ E] in
lemma volume_on_frame (i j : Fin 4) :
    (volumeSquare F).curryLeft (b i) (fun l => b (FormMetric.tripleIndices j l)) =
      if i = j then (-1 : ℝ) ^ (i : ℕ) else 0 := by
  have ht : (volumeSquare F).curryLeft (b i) (fun l => b (FormMetric.tripleIndices j l)) =
      (volumeSquare F) ![b i, b (FormMetric.tripleIndices j 0), b (FormMetric.tripleIndices j 1),
        b (FormMetric.tripleIndices j 2)] := by
    change (volumeSquare F) (Matrix.vecCons (b i) (fun l => b (FormMetric.tripleIndices j l))) = _
    congr 1
    ext l
    fin_cases l <;> rfl
  rw [ht, volumeSquare_apply]
  fin_cases i <;> fin_cases j <;>
    simp [FormMetric.tripleIndices, hF, h0, h1, h2, h3, hb]
  norm_num

include hdim hb h0 h1 h2 h3 hF in
lemma starThree_on_frame (a : MetricForms.Form E 3) (i : Fin 4) :
    starThree g F a ![b i] =
      -((-1 : ℝ) ^ (i : ℕ) * a (fun l => b (FormMetric.tripleIndices i l))) := by
  rw [starThree_apply, pairing_three_eq_sum g hdim b hb]
  simp_rw [volume_on_frame g b hb J h0 h1 h2 h3 F hF]
  simp [mul_comm]

include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_real (ξ : E →L[ℝ] ℝ) (i : Fin 4) :
    starThree g F (wedgeOne ξ (realPart g b)) ![b i] =
      ![-ξ (b 2), ξ (b 3), ξ (b 0), -ξ (b 1)] i := by
  rw [starThree_on_frame g hdim b hb J h0 h1 h2 h3 F hF]
  have ht (i : Fin 4) : (fun l => b (FormMetric.tripleIndices i l)) =
      ![b (FormMetric.tripleIndices i 0),b (FormMetric.tripleIndices i 1),b (FormMetric.tripleIndices i 2)] := by
    ext l
    fin_cases l <;> rfl
  rw [ht, wedgeOne_apply_three]
  fin_cases i <;> simp [FormMetric.tripleIndices, realPart_apply, hb]
  norm_num

include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_imag (ξ : E →L[ℝ] ℝ) (i : Fin 4) :
    starThree g F (wedgeOne ξ (imagPart g b)) ![b i] =
      ![-ξ (b 3), -ξ (b 2), ξ (b 1), ξ (b 0)] i := by
  rw [starThree_on_frame g hdim b hb J h0 h1 h2 h3 F hF]
  have ht (i : Fin 4) : (fun l => b (FormMetric.tripleIndices i l)) =
      ![b (FormMetric.tripleIndices i 0),b (FormMetric.tripleIndices i 1),b (FormMetric.tripleIndices i 2)] := by
    ext l
    fin_cases l <;> rfl
  rw [ht, wedgeOne_apply_three]
  fin_cases i <;> simp [FormMetric.tripleIndices, imagPart_apply, hb]
  norm_num
end TamingCompatibility.AntiInvariantFrame

namespace TamingCompatibility.LocalFrameOperator
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma expansion_at {A B : E → ℝ} {ψ χ : E → MetricForms.Form E 2} {x : E}
    (g : Metric E) (F : MetricForms.Form E 2)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hψ : DifferentiableAt ℝ ψ x) (hχ : DifferentiableAt ℝ χ x) :
    starThree g F (extDeriv (fun y => A y • ψ y + B y • χ y) x) =
      starThree g F (wedgeOne (fderiv ℝ A x) (ψ x)) +
      starThree g F (wedgeOne (fderiv ℝ B x) (χ x)) +
      (A x • starThree g F (extDeriv ψ x) + B x • starThree g F (extDeriv χ x)) := by
  change starThree g F (extDeriv ((fun y => A y • ψ y) + (fun y => B y • χ y)) x) = _
  rw [extDeriv_add (ω₁ := fun y => A y • ψ y) (ω₂ := fun y => B y • χ y) (hA.smul hψ) (hB.smul hχ),
    extDeriv_variable_smul hA hψ, extDeriv_variable_smul hB hχ]
  change starThreeCLM g F
    (A x • extDeriv ψ x + wedgeOne (fderiv ℝ A x) (ψ x) +
      (B x • extDeriv χ x + wedgeOne (fderiv ℝ B x) (χ x))) = _
  simp only [map_add,map_smul,starThreeCLM_apply]
  abel
end TamingCompatibility.LocalFrameOperator

end

end OAI
