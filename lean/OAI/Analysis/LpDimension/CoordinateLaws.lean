import OAI.Analysis.LpDimension.RampRetraction

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

variable {E : Type uE}

def coordinateLaw (μ : Measure (E → ℝ)) (e : E) : Measure ℝ := μ.map (fun v => v e)

instance coordinateLaw_probability (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (e : E) :
    IsProbabilityMeasure (coordinateLaw μ e) := by
  unfold coordinateLaw
  infer_instance

lemma coordinateLaw_integral (μ : Measure (E → ℝ)) (e : E) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂coordinateLaw μ e) = ∫ v, f (v e) ∂μ :=
  integral_map (measurable_pi_apply e).aemeasurable hf.aestronglyMeasurable

lemma coordinateLaw_abs_moment (μ : Measure (E → ℝ)) (e : E) (p : ℝ) :
    (∫ x, |x|^p ∂coordinateLaw μ e) = ∫ v, |v e|^p ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_sq_moment (μ : Measure (E → ℝ)) (e : E) :
    (∫ x, x^2 ∂coordinateLaw μ e) = ∫ v, (v e)^2 ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_exp_moment (μ : Measure (E → ℝ)) (e : E) (s J : ℝ) :
    (∫ x, Real.exp (s*x/J) ∂coordinateLaw μ e) = ∫ v, Real.exp (s*v e/J) ∂μ :=
  coordinateLaw_integral μ e _ (by fun_prop)

lemma coordinateLaw_integrable (μ : Measure (E → ℝ)) (e : E) (f : ℝ → ℝ) (hf : Measurable f) :
    Integrable f (coordinateLaw μ e) ↔ Integrable (fun v => f (v e)) μ :=
  integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply e).aemeasurable

lemma coordinateLaw_ae (μ : Measure (E → ℝ)) (e : E) (P : ℝ → Prop)
    (hP : MeasurableSet {x | P x}) : (∀ᵐ x ∂coordinateLaw μ e, P x) ↔ ∀ᵐ v ∂μ, P (v e) :=
  ae_map_iff (measurable_pi_apply e).aemeasurable hP

lemma coordinateLaw_symmetric (μ : Measure (E → ℝ))
    (hs : μ.map (fun v => -v)=μ) (e : E) : (coordinateLaw μ e).map (fun x => -x)=coordinateLaw μ e := by
  rw [coordinateLaw,Measure.map_map (by fun_prop) (by fun_prop)]
  have hh := congrArg (fun ν : Measure (E → ℝ) => ν.map (fun v => v e)) hs
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hh
  exact hh

lemma coordinateLaw_convolutionPower (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ] (e : E) (n : ℕ) :
    coordinateLaw (convolutionPower μ n) e = convolutionPower (coordinateLaw μ e) n := by
  let L : (E → ℝ) →+ ℝ := { toFun := fun v => v e, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact convolutionPower_map μ L (measurable_pi_apply e) n

lemma convolutionPower_submodule [Fintype E] (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (V : Submodule ℝ (E → ℝ)) (hμ : ∀ᵐ v ∂μ, v ∈ V) (n : ℕ) :
    ∀ᵐ v ∂convolutionPower μ n, v ∈ V := by
  have hV : MeasurableSet (V : Set (E → ℝ)) := V.closed_of_finiteDimensional.measurableSet
  induction n with
  | zero => simp [convolutionPower]
  | succ n ih =>
    rw [convolutionPower,Measure.conv]
    apply (ae_map_iff (show AEMeasurable (fun x : (E → ℝ) × (E → ℝ) => x.1+x.2) _ by fun_prop)
      (show MeasurableSet {v : E → ℝ | v ∈ V} from hV)).mpr
    apply (Measure.ae_prod_iff_ae_ae (p := fun z : (E → ℝ) × (E → ℝ) => z.1+z.2 ∈ V)
      (hV.preimage (by fun_prop))).mpr
    exact ih.mono (fun x hx => hμ.mono (fun y hy => V.add_mem hx hy))

lemma bounded_coordinate_power_integrable (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (e : E) (p B : ℝ) (hp : 0 ≤ p) (hB : ∀ᵐ v ∂μ, |v e| ≤ B) :
    Integrable (fun v => |v e|^p) μ := by
  apply Integrable.of_bound (show Measurable (fun v : E → ℝ => |v e|^p) by fun_prop).aestronglyMeasurable (|B|^p)
  filter_upwards [hB] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (hv.trans (le_abs_self B)) hp

lemma bounded_symmetric_coordinate_exp (μ : Measure (E → ℝ)) [IsProbabilityMeasure μ]
    (hs : μ.map (fun v => -v)=μ) (e : E) (J : ℝ) (hJ : 0 < J)
    (hB : ∀ᵐ v ∂μ, |v e| ≤ J) (s : ℝ) (hs1 : |s|=1) :
    Integrable (fun v => Real.exp (s*v e/J)) μ ∧
    (∫ v, Real.exp (s*v e/J) ∂μ) ≤ 1+(∫ v, (v e)^2 ∂μ)/J^2 := by
  let ν := coordinateLaw μ e
  have hν : ∀ᵐ x ∂ν, |x| ≤ J := (coordinateLaw_ae μ e _ (measurableSet_le (by fun_prop) measurable_const)).mpr hB
  have hi := bounded_exp_integrable ν J hν (s/J)
  have hn := bounded_exp_integrable ν J hν (-(s/J))
  have hsν := coordinateLaw_symmetric μ hs e
  have he := symmetric_integral ν hsν (fun x => Real.exp ((s/J)*x)) hi.aestronglyMeasurable
  have hsq : Integrable (fun x : ℝ => x^2) ν := by
    simpa only [Real.rpow_two,sq_abs] using bounded_abs_moment_integrable ν J 2 hν (by norm_num)
  have hineq : (∫ x, (Real.exp ((s/J)*x)+Real.exp (-((s/J)*x)))/2 ∂ν) ≤
      (∫ x, 1+x^2/J^2 ∂ν) := by
    apply integral_mono_ae ((hi.add (by simpa only [neg_mul] using hn)).div_const 2)
      ((integrable_const 1).add (hsq.div_const _))
    filter_upwards [hν] with x hx
    have hx1 : |(s/J)*x| ≤ 1 := by
      rw [abs_mul,abs_div,hs1,abs_of_pos hJ]
      simpa only [one_div,inv_mul_eq_div] using (div_le_one hJ).mpr hx
    have hh := symmetric_exp_quadratic ((s/J)*x) hx1
    have hs2 : s^2=1 := by nlinarith [sq_abs s,congrArg (fun t : ℝ => t^2) hs1]
    simpa only [Pi.add_apply,mul_pow,div_pow,hs2,one_div,inv_mul_eq_div] using hh
  have he' : (∫ x, Real.exp (-((s/J)*x)) ∂ν) = ∫ x, Real.exp ((s/J)*x) ∂ν := by
    simpa only [mul_neg] using he
  rw [integral_div,integral_add hi (by simpa only [neg_mul] using hn),he',
    integral_add (integrable_const 1) (hsq.div_const _),integral_const,probReal_univ,
    one_smul,integral_div] at hineq
  have hsimp : (fun x : ℝ => Real.exp ((s/J)*x)) = fun x => Real.exp (s*x/J) := by funext x; congr 1; ring
  rw [hsimp] at hi hineq
  refine ⟨(coordinateLaw_integrable μ e _ (by fun_prop)).mp hi,?_⟩
  rw [coordinateLaw_integral μ e _ (by fun_prop),coordinateLaw_integral μ e _ (by fun_prop)] at hineq
  linarith

end SubpolynomialLp

end

end OAI
