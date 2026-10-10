import OAI.Analysis.AncientFlat.Geometry.AnnularGeometry

namespace OAI
noncomputable section
open Set Filter MeasureTheory
namespace ParabolicAnnular
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma time_power_memLp {δ : ℝ} (hδ : 0<δ) :
    MemLp (fun t : ℝ => (-t)^((-1+δ)/2)) 2 (volume.restrict (Ioc (-16) 0)) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-1+δ)) (Ioo 0 16) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).mpr (by linarith)
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.neg ℝ).measurableEmbedding |>.mpr hi
  have he : (Neg.neg : ℝ → ℝ) ⁻¹' Ioo 0 16=Ioo (-16) 0 := by
    ext t; simp only [mem_preimage,mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hn
  change IntegrableOn (fun t : ℝ => (-t)^(-1+δ)) (Ioo (-16) 0) at hn
  rw [IntegrableOn,restrict_Ioo_eq_restrict_Ioc] at hn
  apply (memLp_two_iff_integrable_sq ((measurable_id.neg.pow_const _).aestronglyMeasurable)).mpr
  apply hn.congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-16:ℝ) 0))] with t ht
  have ht0 : 0≤-t := by linarith [ht.2]
  change (-t)^(-1+δ)=((-t)^((-1+δ)/2))^2
  rw [←Real.rpow_natCast,←Real.rpow_mul ht0]
  congr 1
  ring
lemma annular_growth_l2 (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1) :
    ∃ C : ℝ, 0<C ∧ ∀ (u : ℝ → V → ℂ) (M : ℝ), 0≤M →
      (∀ p∈outer, ‖u p.2 p.1‖≤M*(-p.2)^((-1+δ)/2)) →
      ∀ p0∈inner, eLpNorm' (fun p : V × ℝ => windowValue p0 (1/32) u p.2 p.1) (2 : ℝ)
        ((volume.prod volume).restrict (cylinder 2))≤ENNReal.ofReal (C*M) := by
  let θ := (-1+δ)/2
  let g : V × ℝ → ℝ := fun p => ((1/32:ℝ)^4)^θ*(-p.2)^θ
  let μ : Measure (V × ℝ) := (volume.prod volume).restrict (cylinder 2)
  have hcyl : (cylinder 2 : Set (V × ℝ))=Metric.ball 0 2 ×ˢ Ioc (-16) 0 := by
    ext p; simp only [ParabolicInterior.cylinder,mem_ofPred_eq,mem_prod,Metric.mem_ball,dist_zero_right,mem_Ioc]
    norm_num
  have hg : MemLp g 2 μ := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball (0:V) 2)) :=
      isFiniteMeasure_restrict.mpr (measure_ball_lt_top.ne)
    have hh := (time_power_memLp hδ).comp_snd (volume.restrict (Metric.ball (0:V) 2))
    have hh' := hh.const_smul (((1/32:ℝ)^4)^θ)
    change MemLp (fun p : V × ℝ => ((1/32:ℝ)^4)^θ*(-p.2)^((-1+δ)/2)) 2 _ at hh'
    simpa only [Measure.prod_restrict,←hcyl,μ,g,θ] using hh'
  let C := 1+(eLpNorm g 2 μ).toReal
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u M hM hu p0 hp0
  have hmono : eLpNorm' (fun p : V × ℝ => windowValue p0 (1/32) u p.2 p.1) 2 μ ≤
      eLpNorm' (M • g) 2 μ := by
    apply eLpNorm'_mono_ae (by norm_num)
    have hz : ∀ᵐ p : V × ℝ ∂μ, p.2<0 := by
      have ha : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (-16) 0)), t<0 := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-16:ℝ) 0)),
          (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (0:ℝ)))] with t ht hne
        exact lt_of_le_of_ne ht.2 hne
      dsimp only [μ]
      rw [hcyl,←Measure.prod_restrict]
      exact (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_snd measurable_const)).mpr
        (Filter.Eventually.of_forall (fun _ => ha))
    have hm : MeasurableSet (cylinder (2:ℝ) : Set (V × ℝ)) := by
      rw [hcyl]; exact measurableSet_ball.prod measurableSet_Ioc
    filter_upwards [ae_restrict_mem hm,hz] with p hp hpt
    have hmap := annular_window_maps p0 hp0 hp
    have hpow : (-(window p0 (1/32) p).2)^θ≤((1/32:ℝ)^4)^θ*(-p.2)^θ := by
      rw [←Real.mul_rpow (by positivity : (0:ℝ)≤(1/32)^4) (by linarith : 0≤-p.2)]
      apply Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) (neg_pos.mpr hpt)) _ (by dsimp [θ]; linarith)
      dsimp [window]
      nlinarith [hp0.2.2.2]
    have hu' := (hu _ hmap.1).trans (mul_le_mul_of_nonneg_left hpow hM)
    change ‖windowValue p0 (1/32) u p.2 p.1‖≤‖M*g p‖
    rw [norm_mul,Real.norm_of_nonneg hM,Real.norm_of_nonneg (show 0≤g p by exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by linarith) _))]
    exact hu'
  calc
    _ ≤ eLpNorm' (M • g) 2 μ := hmono
    _ = eLpNorm (M • g) 2 μ := by
      simpa using (eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num)
        (hg.const_smul M).aestronglyMeasurable).symm
    _ = ENNReal.ofReal M*eLpNorm g 2 μ := by
      rw [eLpNorm_const_smul]
      congr 1
      rw [←ofReal_norm,Real.norm_of_nonneg hM]
    _ = ENNReal.ofReal (M*(eLpNorm g 2 μ).toReal) := by
      rw [ENNReal.ofReal_mul hM,ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
    _ ≤ ENNReal.ofReal (C*M) := ENNReal.ofReal_le_ofReal (by dsimp [C]; nlinarith)
end ParabolicAnnular

end

end OAI
