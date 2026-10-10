import OAI.Analysis.FiniteFactor.Sampling.Weights

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem unitInterval_split (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitIntervalMeasure = volume.restrict (Set.Ioc (0 : ℝ) c) + volume.restrict (Set.Ioc c 1) := by
  unfold unitIntervalMeasure
  rw [restrict_Ico_eq_restrict_Ioc,← Set.Ioc_union_Ioc_eq_Ioc hc hc1,
    Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]

theorem map_interval_affine (a b c d : ℝ) (hc : 0 < c) :
    (volume.restrict (Set.Ioc a b)).map (fun x => c*x+d) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Set.Ioc (c*a+d) (c*b+d)) := by
  have hp : (fun x : ℝ => c*x+d) ⁻¹' Set.Ioc (c*a+d) (c*b+d) = Set.Ioc a b := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Ioc,add_lt_add_iff_right,add_le_add_iff_right,
      mul_lt_mul_iff_right₀ hc,mul_le_mul_iff_right₀ hc]
  have hmap : volume.map (fun x : ℝ => c*x+d) = ENNReal.ofReal c⁻¹ • volume := by
    have he : (fun x : ℝ => c*x+d) = (fun x : ℝ => x+d) ∘ (fun x : ℝ => c*x) := rfl
    rw [he,← Measure.map_map (by fun_prop) (by fun_prop),Real.map_volume_mul_left hc.ne',
      Measure.map_smul _ (by fun_prop),
      (measurePreserving_add_right (volume : Measure ℝ) d).map_eq,abs_of_pos (inv_pos.mpr hc)]
  rw [← hp,← Measure.restrict_map (f := fun x : ℝ => c*x+d) (by fun_prop) measurableSet_Ioc,
    hmap,Measure.restrict_smul]

/-- The uncut diagonal model moves z by v times its endpoint distance. -/
def samplingTransport (v z : ℝ) : ℝ := z+v*samplingDistance z

/-- Exact density of the two affine branches of the uncut transport. -/
def samplingTransportDensity (v s : ℝ) : ℝ :=
  if s ≤ (1+v)/2 then 1/(1+v) else 1/(1-v)

theorem samplingTransportDensity_measurable :
    Measurable (fun p : ℝ × ℝ => samplingTransportDensity p.1 p.2) := by
  unfold samplingTransportDensity
  exact Measurable.ite (measurableSet_le measurable_snd ((measurable_const.add measurable_fst).div_const 2))
    (by fun_prop) (by fun_prop)

/-- This is the actual push-forward density, not an assumed ideal moment. -/
theorem samplingTransport_density (v : ℝ) (hv : 0 ≤ v) (hv1 : v < 1) :
    unitIntervalMeasure.map (samplingTransport v) =
      unitIntervalMeasure.withDensity (fun s => ENNReal.ofReal (samplingTransportDensity v s)) := by
  let c := (1+v)/2
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hleft : (volume.restrict (Set.Ioc (0 : ℝ) (1/2))).map (samplingTransport v) =
      ENNReal.ofReal (1/(1+v)) • volume.restrict (Set.Ioc (0 : ℝ) c) := by
    have he : samplingTransport v =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (1/2))] (fun z => (1+v)*z+0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      unfold samplingTransport samplingDistance
      rw [min_eq_left (by linarith [hz.2])]
      ring
    rw [Measure.map_congr he,map_interval_affine _ _ _ _ (by linarith)]
    simp only [mul_zero,add_zero,one_div]
    congr 3
  have hright : (volume.restrict (Set.Ioc (1/2 : ℝ) 1)).map (samplingTransport v) =
      ENNReal.ofReal (1/(1-v)) • volume.restrict (Set.Ioc c (1 : ℝ)) := by
    have he : samplingTransport v =ᵐ[volume.restrict (Set.Ioc (1/2 : ℝ) 1)] (fun z => (1-v)*z+v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      unfold samplingTransport samplingDistance
      rw [min_eq_right (by linarith [hz.1])]
      ring
    rw [Measure.map_congr he,map_interval_affine _ _ _ _ (by linarith)]
    have hc' : (1-v)*(1/2)+v = c := by dsimp [c]; ring
    rw [hc',show (1-v)*1+v = 1 by ring]
    simp [one_div]
  have hdleft : (volume.restrict (Set.Ioc (0 : ℝ) c)).withDensity
      (fun s => ENNReal.ofReal (samplingTransportDensity v s)) =
      ENNReal.ofReal (1/(1+v)) • volume.restrict (Set.Ioc (0 : ℝ) c) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp [samplingTransportDensity,show z ≤ (1+v)/2 from hz.2]
  have hdright : (volume.restrict (Set.Ioc c (1 : ℝ))).withDensity
      (fun s => ENNReal.ofReal (samplingTransportDensity v s)) =
      ENNReal.ofReal (1/(1-v)) • volume.restrict (Set.Ioc c (1 : ℝ)) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp [samplingTransportDensity,show ¬z ≤ (1+v)/2 from not_le.mpr hz.1]
  conv_lhs => rw [unitInterval_split (1/2) (by norm_num) (by norm_num)]
  have htm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
  rw [Measure.map_add _ _ htm,hleft,hright]
  conv_rhs => rw [unitInterval_split c hc hc1]
  rw [withDensity_add_measure,hdleft,hdright]

end
end FiniteFactor

end OAI
