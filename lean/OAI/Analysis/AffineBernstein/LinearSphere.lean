import Mathlib
import OAI.Analysis.AffineBernstein.ProjectiveCone

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section DependencyScope
open Filter
open scoped Topology

section LinearSphere
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma linear_cone_lintegral (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : E) (r : ℝ), 0 < r → f (r • x) = f x) :
    (∫⁻ x in A ⁻¹' (Metric.ball (0:E) 1 \ {0}), f (A x) ∂μ) =
    ∫⁻ e : Metric.sphere (0:E) 1, f (A e) *
      ENNReal.ofReal ((‖A e‖⁻¹)^((Module.finrank ℝ E - 1)+1) /
        (((Module.finrank ℝ E - 1)+1:ℕ):ℝ)) ∂μ.toSphere := by
  let Φ := homeomorphUnitSphereProd E
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let U : Set (Metric.sphere (0:E) 1 × Ioi (0:ℝ)) :=
    {q | (q.2:ℝ) * ‖A (q.1:E)‖ < 1}
  have hU : MeasurableSet U := by
    apply measurableSet_lt _ measurable_const
    exact (measurable_subtype_coe.comp measurable_snd).mul
      (A.continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst)).norm
  have hnorm (z : ↑(({0}:Set E)ᶜ)) :
      ‖A z‖ = ((Φ z).2:ℝ) * ‖A ((Φ z).1:E)‖ := by
    have hz : (z:E) = ((Φ z).2:ℝ) • ((Φ z).1:E) := by
      simpa only [Φ,homeomorphUnitSphereProd_symm_apply_coe] using
        (congrArg Subtype.val (Φ.symm_apply_apply z)).symm
    conv_lhs => rw [hz]
    rw [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (Φ z).2.property]
  have hsub : Subtype.val '' (Φ ⁻¹' U) = A ⁻¹' (Metric.ball (0:E) 1 \ {0}) := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,?_⟩
      · rw [Metric.mem_ball,dist_zero_right,hnorm]
        exact hz
      · intro hz0
        have hzero : (z:E) = 0 := A.injective (by simpa using hz0)
        exact z.property hzero
    · intro hx
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hx.2
        simp [hx0]
      refine ⟨⟨x,hx0⟩,?_,rfl⟩
      change ((Φ ⟨x,hx0⟩).2:ℝ) * ‖A ((Φ ⟨x,hx0⟩).1:E)‖ < 1
      rw [← hnorm]
      simpa only [Metric.mem_ball,dist_zero_right] using hx.1
  have heq : (∫⁻ q in U, f (A ((Φ.symm q):E)) ∂μ.toSphere.prod ν) =
      ∫⁻ x in A ⁻¹' (Metric.ball (0:E) 1 \ {0}), f (A x) ∂μ := by
    rw [← μ.measurePreserving_homeomorphUnitSphereProd.setLIntegral_comp_preimage_emb
      Φ.measurableEmbedding (fun q => f (A ((Φ.symm q):E))) U]
    simp only [Φ,Homeomorph.symm_apply_apply]
    rw [setLIntegral_subtype (measurableSet_singleton (0:E)).compl _ (fun x : E => f (A x)),hsub]
  rw [← heq]
  have hg : Measurable (fun q : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => f (A q.1)) :=
    hf.comp (A.continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst))
  have hreplace : (∫⁻ q in U, f (A ((Φ.symm q):E)) ∂μ.toSphere.prod ν) =
      ∫⁻ q in U, f (A q.1) ∂μ.toSphere.prod ν := by
    apply setLIntegral_congr_fun hU
    intro q _
    simp only [Φ,homeomorphUnitSphereProd_symm_apply_coe,map_smul]
    exact hscale _ _ q.2.property
  rw [hreplace,← lintegral_indicator hU,lintegral_prod _ ((hg.indicator hU).aemeasurable)]
  apply lintegral_congr
  intro e
  have he0 : (e:E) ≠ 0 := by
    intro he0
    simpa [he0] using e.property
  have ha : 0 < ‖A e‖ := norm_pos_iff.mpr (fun hz => he0 (A.injective (by simpa using hz)))
  let ar : Ioi (0:ℝ) := ⟨‖A e‖⁻¹,inv_pos.mpr ha⟩
  have hind : (fun t : Ioi (0:ℝ) => U.indicator (fun q => f (A q.1)) (e,t)) =
      (Iio ar).indicator (fun _ => f (A e)) := by
    funext t
    simp only [Set.indicator,Set.mem_ofPred_eq,Set.mem_Iio,U,ar]
    congr 1
    change ((t:ℝ)*‖A e‖ < 1) = ((t:ℝ) < ‖A e‖⁻¹)
    apply propext
    rw [inv_eq_one_div,lt_div_iff₀ ha]
  rw [hind,lintegral_indicator measurableSet_Iio,lintegral_const,
    Measure.restrict_apply_univ]
  simp only [ν,Measure.volumeIoiPow_apply_Iio,ar,Nat.cast_add,Nat.cast_one]


/- Exact projective change of variables on Haar-normalized sphere area. The
Jacobian is derived from the linear volume determinant and polar coordinates.
The ambient integrand is homogeneous of degree zero; no integrability is assumed. -/
lemma sphere_lintegral_linear_jacobian (μ : Measure E) [μ.IsAddHaarMeasure]
    [Nontrivial E] (A : E ≃L[ℝ] E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : E) (r : ℝ), 0 < r → f (r • x) = f x) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) =
    ENNReal.ofReal |A.toLinearMap.det| *
      ∫⁻ e : Metric.sphere (0:E) 1,
        f (A e) * ENNReal.ofReal ((‖A e‖⁻¹)^(Module.finrank ℝ E)) ∂μ.toSphere := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hdim : Module.finrank ℝ E - 1 + 1 = Module.finrank ℝ E := Nat.sub_add_cancel hd
  let S := Metric.ball (0:E) 1 \ {0}
  have hS : MeasurableSet (A ⁻¹' S) :=
    (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton 0)).preimage A.continuous.measurable
  have hj := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ:=μ) hS
    (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) A.injective.injOn f
  rw [Set.image_preimage_eq _ A.surjective] at hj
  change (∫⁻ x in S, f x ∂μ) =
    ∫⁻ x in A ⁻¹' S, ENNReal.ofReal |A.toLinearMap.det| * f (A x) ∂μ at hj
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hj
  have hr := sphere_lintegral_mul_radial_eq μ
    (hf.comp measurable_subtype_coe) (fun e r hr _ => (hscale e r hr).symm)
  rw [hdim] at hr
  have hc := linear_cone_lintegral μ A f hf hscale
  rw [hdim] at hc
  have hsplit : (∫⁻ e : Metric.sphere (0:E) 1, f (A e) *
      ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E / (Module.finrank ℝ E:ℝ)) ∂μ.toSphere) =
      (∫⁻ e : Metric.sphere (0:E) 1,
        f (A e) * ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E) ∂μ.toSphere) *
        ENNReal.ofReal (1 / (Module.finrank ℝ E:ℝ)) := by
    have he (e : Metric.sphere (0:E) 1) :
        ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E / (Module.finrank ℝ E:ℝ)) =
        ENNReal.ofReal (‖A e‖⁻¹ ^ Module.finrank ℝ E) *
          ENNReal.ofReal (1 / (Module.finrank ℝ E:ℝ)) := by
      rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)]
      congr 1
      ring
    simp_rw [he,← mul_assoc]
    exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
  apply (ENNReal.mul_left_inj (by positivity : ENNReal.ofReal (1 / (Module.finrank ℝ E:ℝ)) ≠ 0)
    ENNReal.ofReal_ne_top).mp
  rw [hr,hj,hc,hsplit,mul_assoc]

end LinearSphere

end DependencyScope
end AffineBernstein
end

end OAI
