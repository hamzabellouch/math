import Mathlib
import OAI.Probability.SphericalField.Cascade.Recursion

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
lemma stablePoisson_descendant_transform_marked {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    [Nonempty S] [Nonempty C] [Nonempty D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ) {F : S → ℝ} (hF : Measurable F) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod (ν.prod ρ))).map
      (Measure.map (fun p : ℝ×(S×C) => (p.1+F p.2.1,(p.2.1,T p.2)))) =
      poissonRandomMeasureLaw ((stableLogIntensity b).prod
        ((ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*F s)))).prod θ)) := by
  rw [poissonRandomMeasureLaw_map _ (by fun_prop)]
  congr 1
  exact stableIntensity_descendant_transform_marked ν ρ θ hb T hT hLaw hF

lemma normalizedMeasure_prod {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [SFinite ν] [SFinite ρ]
    (hν0 : ν univ ≠ 0) (hνf : ν univ ≠ ⊤) :
    normalizedMeasure (ν.prod ρ) = (normalizedMeasure ν).prod (normalizedMeasure ρ) := by
  unfold normalizedMeasure
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  congr 1
  rw [← univ_prod_univ,Measure.prod_prod,ENNReal.mul_inv (Or.inl hν0) (Or.inl hνf)]

lemma exponentialMarkTilt_prod_add {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (b : ℝ) {f : S → ℝ} {g : T → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hIf : Integrable (fun s => Real.exp (b*f s)) ν) :
    exponentialMarkTilt (ν.prod ρ) b (fun p => f p.1+g p.2) =
      (exponentialMarkTilt ν b f).prod (exponentialMarkTilt ρ b g) := by
  have hνmass : (ν.withDensity (fun s => ENNReal.ofReal (Real.exp (b*f s)))) univ =
      ENNReal.ofReal (∫ s, Real.exp (b*f s) ∂ν) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hIf (ae_of_all _ fun s => (Real.exp_pos _).le)).symm
  have hd : (fun p : S×T => ENNReal.ofReal (Real.exp (b*(f p.1+g p.2)))) =
      (fun p : S×T => ENNReal.ofReal (Real.exp (b*f p.1))* ENNReal.ofReal (Real.exp (b*g p.2))) := by
    funext p
    rw [mul_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold exponentialMarkTilt
  rw [hd,← prod_withDensity ((hf.const_mul b).exp.ennreal_ofReal) ((hg.const_mul b).exp.ennreal_ofReal)]
  apply normalizedMeasure_prod
  · rw [hνmass]; exact ENNReal.ofReal_ne_zero_iff.mpr (integral_exp_pos hIf)
  · rw [hνmass]; exact ENNReal.ofReal_ne_top

lemma fractional_log_moment_prod_add {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) (ρ : Measure T) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (b : ℝ) {f : S → ℝ} {g : T → ℝ}
    (hIf : Integrable (fun s => Real.exp (b*f s)) ν)
    (hIg : Integrable (fun t => Real.exp (b*g t)) ρ) :
    Real.log (∫ p, Real.exp (b*(f p.1+g p.2)) ∂ν.prod ρ)/b =
      Real.log (∫ s, Real.exp (b*f s) ∂ν)/b + Real.log (∫ t, Real.exp (b*g t) ∂ρ)/b := by
  simp_rw [mul_add,Real.exp_add]
  rw [integral_prod_mul (fun s => Real.exp (b*f s)) (fun t => Real.exp (b*g t)),Real.log_mul (integral_exp_pos hIf).ne' (integral_exp_pos hIg).ne',add_div]

def productMarkLaw {S T : Type} [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T) : ProbabilityMeasure (S×T) :=
  ⟨(ν : Measure S).prod (ρ : Measure T),inferInstance⟩

theorem finiteCascadeLogRecursion_add_product {X Y S T : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace S] [MeasurableSpace T]
    (ν : ProbabilityMeasure S) (ρ : ProbabilityMeasure T)
    (step₁ : X×S → X) (step₂ : Y×T → Y)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    {H : X → ℝ} {G : Y → ℝ}
    (hIH : finiteCascadeFractionalIntegrable ν step₁ H n z)
    (hIG : finiteCascadeFractionalIntegrable ρ step₂ G n z) (x : X) (y : Y) :
    finiteCascadeLogRecursion (productMarkLaw ν ρ)
      (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n z
        (fun q => H q.1+G q.2) (x,y) =
      finiteCascadeLogRecursion ν step₁ n z H x + finiteCascadeLogRecursion ρ step₂ n z G y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rcases hIH with ⟨hHroot,hHtail⟩
    rcases hIG with ⟨hGroot,hGtail⟩
    conv_lhs => rw [finiteCascadeLogRecursion]
    change Real.log (∫ p : S×T, Real.exp (z 0 *
      finiteCascadeLogRecursion (productMarkLaw ν ρ)
        (fun p : (X×Y)×(S×T) => (step₁ (p.1.1,p.2.1),step₂ (p.1.2,p.2.2))) n (fun i => z i.succ)
          (fun q => H q.1+G q.2) (step₁ (x,p.1),step₂ (y,p.2))) ∂(ν : Measure S).prod (ρ : Measure T))/(z 0) = _
    simp_rw [ih (fun i => z i.succ) (fun i => hz i.succ) hHtail hGtail]
    exact fractional_log_moment_prod_add (ν : Measure S) (ρ : Measure T) (z 0) (hHroot x) (hGroot y)

lemma real_quadratic_complete_square {b : ℝ} (hb : b ≠ 0) (c d y : ℝ) :
    Real.exp (-b*y^2+c*y+d) =
      Real.exp (d+c^2/(4*b))*Real.exp (-b*(y-c/(2*b))^2) := by
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

lemma real_quadratic_integrable {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-b*y^2+c*y+d)) := by
  simp_rw [real_quadratic_complete_square hb.ne']
  exact ((integrable_exp_neg_mul_sq hb).comp_sub_right (c/(2*b))).const_mul _

lemma real_quadratic_integral {b : ℝ} (hb : 0 < b) (c d : ℝ) :
    (∫ y : ℝ, Real.exp (-b*y^2+c*y+d)) =
      Real.exp (d+c^2/(4*b))*Real.sqrt (Real.pi/b) := by
  simp_rw [real_quadratic_complete_square hb.ne']
  rw [integral_const_mul, integral_sub_right_eq_self (fun y : ℝ => Real.exp (-b*y^2)),integral_gaussian]

lemma standardGaussian_quadratic_density (a c d y : ℝ) :
    gaussianPDFReal 0 1 y * Real.exp (a*y^2+c*y+d) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*y^2+c*y+d) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma standardGaussian_quadratic_integrable {a : ℝ} (ha : a < 1/2) (c d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (a*y^2+c*y+d)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [smul_eq_mul]
  have he : (fun y : ℝ => (gaussianPDF 0 1 y).toReal * Real.exp (a*y^2+c*y+d)) =
      (fun y : ℝ => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-a)*y^2+c*y+d)) := by
    funext y
    rw [toReal_gaussianPDF]
    exact standardGaussian_quadratic_density a c d y
  rw [he]
  exact (real_quadratic_integrable (by linarith : 0 < 1/2-a) c d).const_mul _

end SphericalPerceptron
end
end
end

end OAI
