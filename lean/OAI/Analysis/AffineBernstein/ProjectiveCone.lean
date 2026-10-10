import Mathlib
import OAI.Analysis.AffineBernstein.ProjectiveWeightContinuity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral

section ProjectiveCone
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/- Ordinary-volume computation of a projective cone. Together with polar
coordinates this yields the hemisphere chart density without assuming a
surface-area formula. -/
theorem projective_cone_lintegral (f : WithLp 2 (F × ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hscale : ∀ (x : WithLp 2 (F × ℝ)) (t : ℝ), 0 < t → f (t • x) = f x) :
    (∫⁻ t in Ioi (0:ℝ), ∫⁻ x : F,
      if ‖WithLp.toLp 2 (x,t)‖ < 1 then f (WithLp.toLp 2 (x,t)) else 0) =
        ∫⁻ x : F, ENNReal.ofReal (‖WithLp.toLp 2 (x,(1:ℝ))‖⁻¹ ^
          (Module.finrank ℝ F+1) / (Module.finrank ℝ F+1)) * f (WithLp.toLp 2 (x,(1:ℝ))) := by
  let k := Module.finrank ℝ F
  let p := fun x : F => WithLp.toLp 2 (x,(1:ℝ))
  let G : F × ℝ → ℝ≥0∞ := fun q =>
    if ‖WithLp.toLp 2 q‖ < 1 then f (WithLp.toLp 2 q) else 0
  have hG : Measurable G := by
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) measurable_const
    · exact hf.comp (MeasurableEquiv.toLp 2 (F × ℝ)).measurable
    · exact measurable_const
  let H : ℝ → F → ℝ≥0∞ := fun t x =>
    if t < ‖p x‖⁻¹ then ENNReal.ofReal (t^k)*f (p x) else 0
  have hH : Measurable (Function.uncurry H) := by
    apply Measurable.ite
    · apply measurableSet_lt measurable_fst
      dsimp [p]
      fun_prop
    · exact (by fun_prop : Measurable (fun q : ℝ × F => ENNReal.ofReal (q.1^k))).mul
        (hf.comp (by dsimp [p]; fun_prop))
    · exact measurable_const
  have hs (t : ℝ) (ht : 0 < t) : (∫⁻ x : F, G (x,t)) = ∫⁻ x : F, H t x := by
    rw [← lintegral_smul_jacobian volume (fun x : F => G (x,t)) ht]
    rw [← lintegral_const_mul _ (show Measurable (fun x : F => G (t • x,t)) from
      hG.comp (by fun_prop))]
    apply lintegral_congr
    intro x
    have he : WithLp.toLp 2 (t • x,t) = t • p x := by
      rw [← WithLp.toLp_smul]
      congr 1
      simp [Prod.smul_mk]
    dsimp only [G,H]
    rw [he,hscale _ t ht,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hn : 0 < ‖p x‖ := projective_norm_pos x
    simp only [← one_div ‖p x‖,lt_div_iff₀ hn]
    split_ifs <;> simp [k]
  calc
    _ = ∫⁻ t in Ioi (0:ℝ), ∫⁻ x : F, H t x := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact hs t ht
    _ = ∫⁻ x : F, ∫⁻ t in Ioi (0:ℝ), H t x :=
      lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      have hn : 0 < ‖p x‖⁻¹ := inv_pos.mpr (projective_norm_pos x)
      change (∫⁻ t in Ioi (0:ℝ), (Iio ‖p x‖⁻¹).indicator
        (fun t => ENNReal.ofReal (t^k)*f (p x)) t) = _
      rw [lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
      have he : Iio ‖p x‖⁻¹ ∩ Ioi (0:ℝ) = Ioo 0 ‖p x‖⁻¹ := by ext t; simp [and_comm]
      rw [he,lintegral_mul_const _ (by fun_prop),lintegral_pow_Ioo hn]

end ProjectiveCone

/- A homogeneous quantity which expands on inward rays has its spherical
integral controlled by its integral over the punctured unit ball. The exact
radial Haar normalization is retained. -/
lemma sphere_lintegral_mul_radial_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞}
    (hf : Measurable (fun e : Metric.sphere (0:E) 1 => f e))
    (hscale : ∀ (e : Metric.sphere (0:E) 1) (r : ℝ), 0 < r → r < 1 → f e = f (r • (e:E))) :
    (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
      ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) =
        ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
  let Φ := homeomorphUnitSphereProd E
  let ν := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  let r₁ : Ioi (0:ℝ) := ⟨1,by change (0:ℝ) < 1; exact one_pos⟩
  let U : Set (Metric.sphere (0:E) 1 × Ioi (0:ℝ)) := univ ×ˢ Iio r₁
  have hU : MeasurableSet U := MeasurableSet.univ.prod measurableSet_Iio
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hprod : (∫⁻ q in U, f q.1 ∂μ.toSphere.prod ν) =
      (∫⁻ e : Metric.sphere (0:E) 1, f e ∂μ.toSphere) *
        ENNReal.ofReal (1 / ((Module.finrank ℝ E - 1 + 1 : ℕ):ℝ)) := by
    dsimp only [U]
    rw [setLIntegral_prod (fun q : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => f q.1)
      ((hf.comp measurable_fst).aemeasurable)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const _ hf]
    simp [ν,r₁,Measure.volumeIoiPow_apply_Iio]
  have hsub : Subtype.val '' (Φ ⁻¹' U) = Metric.ball (0:E) 1 \ {0} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,z.property⟩
      rw [Metric.mem_ball,dist_zero_right]
      have hz2 : ((Φ z).2:ℝ) < 1 := hz.2
      simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe] using hz2
    · intro hx
      refine ⟨⟨x,hx.2⟩,?_,rfl⟩
      change True ∧ ((Φ ⟨x,hx.2⟩).2:ℝ) < 1
      exact ⟨trivial,by simpa [Φ,homeomorphUnitSphereProd_apply_snd_coe,
        Metric.mem_ball,dist_zero_right] using hx.1⟩
  have heq : (∫⁻ q in U, f ((Φ.symm q):E) ∂μ.toSphere.prod ν) =
      ∫⁻ x in Metric.ball (0:E) 1 \ {0}, f x ∂μ := by
    rw [← hmp.setLIntegral_comp_preimage_emb Φ.measurableEmbedding
      (fun q => f ((Φ.symm q):E)) U]
    simp only [Φ,Homeomorph.symm_apply_apply]
    rw [setLIntegral_subtype (measurableSet_singleton (0:E)).compl,hsub]
  rw [← hprod,← heq]
  apply setLIntegral_congr_fun hU
  intro q hq
  have hr : (q.2:ℝ) < 1 := hq.2
  simpa only [Φ,homeomorphUnitSphereProd_symm_apply_coe] using hscale q.1 q.2 q.2.property hr

end AffineBernstein
end

end OAI
