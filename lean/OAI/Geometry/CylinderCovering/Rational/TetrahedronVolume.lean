import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

open Set MeasureTheory

noncomputable section

namespace RationalTetrahedron
open SlopeRational

private theorem hpos : 0 < physicalScale := by unfold physicalScale; positivity

private def tripleEquiv : (ℝ × (ℝ × ℝ)) ≃ᵐ Space :=
  ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow.symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

private theorem tripleEquiv_apply (p : ℝ × (ℝ × ℝ)) :
    tripleEquiv p = RuledApproximation.vec3 p.2.1 p.2.2 p.1 := by
  ext i
  fin_cases i <;> rfl

private theorem tripleEquiv_measurePreserving :
    MeasurePreserving tripleEquiv volume volume := by
  apply (PiLp.volume_preserving_toLp (Fin 3)).comp
  apply (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
  exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm

private theorem mem_tetrahedron_iff (z : Space) : z ∈ referenceTetrahedron ↔
    z 2 / physicalScale ∈ Icc (-(1/2:ℝ)) (1/2) ∧
    |z 0| ≤ (1/2+z 2 / physicalScale)/2 ∧
    |z 1| ≤ (1/2-z 2 / physicalScale)/2 := by
  constructor
  · rintro ⟨t,ht0,ht1,hx,hy,hz⟩
    rw [hz, mul_div_cancel_left₀ _ hpos.ne']
    exact ⟨⟨ht0,ht1⟩,hx,hy⟩
  · rintro ⟨⟨ht0,ht1⟩,hx,hy⟩
    exact ⟨z 2/physicalScale,ht0,ht1,hx,hy,(mul_div_cancel₀ _ hpos.ne').symm⟩

private theorem referenceTetrahedron_isClosed : IsClosed referenceTetrahedron := by
  have he : referenceTetrahedron = {z : Space |
      -(1/2:ℝ) ≤ z 2/physicalScale ∧ z 2/physicalScale ≤ 1/2 ∧
      |z 0| ≤ (1/2+z 2/physicalScale)/2 ∧
      |z 1| ≤ (1/2-z 2/physicalScale)/2} := by
    ext z
    simpa only [mem_ofPred_eq, mem_Icc, and_assoc] using mem_tetrahedron_iff z
  rw [he]
  exact (isClosed_le (f := fun _ : Space => -(1/2:ℝ))
      (g := fun z => z 2/physicalScale) (by fun_prop) (by fun_prop)).inter
    ((isClosed_le (f := fun z : Space => z 2/physicalScale)
      (g := fun _ => (1/2:ℝ)) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Space => |z 0|)
        (g := fun z => (1/2+z 2/physicalScale)/2) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Space => |z 1|)
          (g := fun z => (1/2-z 2/physicalScale)/2) (by fun_prop) (by fun_prop))))

private theorem referenceTetrahedron_isCompact : IsCompact referenceTetrahedron := by
  let box := Icc (-physicalScale/2) (physicalScale/2) ×ˢ
    (Icc (-(1/2:ℝ)) (1/2) ×ˢ Icc (-(1/2:ℝ)) (1/2))
  have hb : IsCompact (tripleEquiv '' box) :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
      (by rw [show (tripleEquiv : (ℝ × (ℝ × ℝ)) → Space) =
        (fun p => RuledApproximation.vec3 p.2.1 p.2.2 p.1) from funext tripleEquiv_apply]
          unfold RuledApproximation.vec3
          fun_prop)
  apply hb.of_isClosed_subset referenceTetrahedron_isClosed
  intro z hz
  obtain ⟨t,ht0,ht1,hx,hy,hz2⟩ := hz
  refine ⟨(z 2,(z 0,z 1)),?_,?_⟩
  · change z 2 ∈ Icc (-physicalScale/2) (physicalScale/2) ∧
      z 0 ∈ Icc (-(1/2:ℝ)) (1/2) ∧ z 1 ∈ Icc (-(1/2:ℝ)) (1/2)
    have hxt : |z 0| ≤ 1/2 := by linarith
    have hyt : |z 1| ≤ 1/2 := by linarith
    refine ⟨?_,abs_le.mp hxt,abs_le.mp hyt⟩
    rw [hz2]
    constructor <;> nlinarith [hpos]
  · rw [tripleEquiv_apply]
    ext i
    fin_cases i <;> rfl

private theorem space_integral_triple (f : Space → ℝ) :
    (∫ z, f z) = ∫ p : ℝ × (ℝ × ℝ), f (RuledApproximation.vec3 p.2.1 p.2.2 p.1) := by
  have h := tripleEquiv_measurePreserving.integral_comp tripleEquiv.measurableEmbedding f
  simpa only [tripleEquiv_apply] using h.symm

private theorem space_integrable_triple (f : Space → ℝ) :
    Integrable (fun p : ℝ × (ℝ × ℝ) => f (RuledApproximation.vec3 p.2.1 p.2.2 p.1)) ↔
      Integrable f := by
  have h := tripleEquiv_measurePreserving.integrable_comp_emb tripleEquiv.measurableEmbedding
    (g := f)
  simpa only [Function.comp_def, tripleEquiv_apply] using h

private theorem volume_by_slices :
    volume.real referenceTetrahedron = ∫ t : ℝ,
      volume.real {p : ℝ × ℝ | RuledApproximation.vec3 p.1 p.2 t ∈ referenceTetrahedron} := by
  have hK := referenceTetrahedron_isCompact.measurableSet
  have hfin : volume referenceTetrahedron ≠ ⊤ := referenceTetrahedron_isCompact.measure_lt_top.ne
  have hi : IntegrableOn (fun _ : Space => (1:ℝ)) referenceTetrahedron :=
    integrableOn_const hfin
  calc
    volume.real referenceTetrahedron = ∫ z in referenceTetrahedron, (1:ℝ) := by simp
    _ = ∫ t : ℝ, ∫ p : ℝ × ℝ,
        referenceTetrahedron.indicator (fun _ => (1:ℝ)) (RuledApproximation.vec3 p.1 p.2 t) := by
      rw [← integral_indicator hK, space_integral_triple]
      rw [Measure.volume_eq_prod, integral_prod _
        (by simpa only [Measure.volume_eq_prod] using
          (space_integrable_triple _).mpr (hi.integrable_indicator hK))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      have hm : MeasurableSet {p : ℝ × ℝ |
          RuledApproximation.vec3 p.1 p.2 t ∈ referenceTetrahedron} :=
        hK.preimage (by unfold RuledApproximation.vec3; fun_prop)
      change (∫ p : ℝ × ℝ,
        ({p : ℝ × ℝ | RuledApproximation.vec3 p.1 p.2 t ∈ referenceTetrahedron}).indicator
          (fun _ => (1:ℝ)) p) = _
      rw [integral_indicator hm]
      simp

private theorem tetrahedron_slice (t : ℝ) :
    {p : ℝ × ℝ | RuledApproximation.vec3 p.1 p.2 t ∈ referenceTetrahedron} =
      if t/physicalScale ∈ Icc (-(1/2:ℝ)) (1/2) then
        Icc (-(1/2+t/physicalScale)/2) ((1/2+t/physicalScale)/2) ×ˢ
        Icc (-(1/2-t/physicalScale)/2) ((1/2-t/physicalScale)/2)
      else ∅ := by
  ext p
  change (RuledApproximation.vec3 p.1 p.2 t ∈ referenceTetrahedron) ↔ _
  rw [mem_tetrahedron_iff]
  change (t/physicalScale ∈ Icc (-(1/2:ℝ)) (1/2) ∧
    |p.1| ≤ (1/2+t/physicalScale)/2 ∧ |p.2| ≤ (1/2-t/physicalScale)/2) ↔ _
  by_cases ht : t/physicalScale ∈ Icc (-(1/2:ℝ)) (1/2)
  · rw [ite_eq_left ht]
    simp only [ht, true_and, mem_prod, mem_Icc, neg_div, ← abs_le]
  · rw [ite_eq_right ht]
    simp only [ht, false_and, mem_empty_iff_false]

private theorem scaled_height_mem_iff (t : ℝ) :
    t/physicalScale ∈ Icc (-(1/2:ℝ)) (1/2) ↔
      t ∈ Icc (-physicalScale/2) (physicalScale/2) := by
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · have h := (le_div_iff₀ hpos).1 hl
      linarith
    · have h := (div_le_iff₀ hpos).1 hu
      linarith
  · rintro ⟨hl,hu⟩
    constructor
    · apply (le_div_iff₀ hpos).2
      linarith
    · apply (div_le_iff₀ hpos).2
      linarith

private theorem volume_slice_integral :
    volume.real referenceTetrahedron =
      ∫ t in Icc (-physicalScale/2) (physicalScale/2),
        (1/2+t/physicalScale)*(1/2-t/physicalScale) := by
  rw [volume_by_slices, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  rw [tetrahedron_slice]
  by_cases ht : t/physicalScale ∈ Icc (-(1/2:ℝ)) (1/2)
  · rw [ite_eq_left ht, Set.indicator_of_mem ((scaled_height_mem_iff t).1 ht)]
    have hx : 0 ≤ 1/2+t/physicalScale := by linarith [ht.1]
    have hy : 0 ≤ 1/2-t/physicalScale := by linarith [ht.2]
    have hlx : (1/2+t/physicalScale)/2-(-(1/2+t/physicalScale)/2) =
        1/2+t/physicalScale := by ring
    have hly : (1/2-t/physicalScale)/2-(-(1/2-t/physicalScale)/2) =
        1/2-t/physicalScale := by ring
    simp only [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, ENNReal.toReal_mul, hlx, hly,
      ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy]
  · rw [ite_eq_right ht, Set.indicator_of_notMem (fun h => ht ((scaled_height_mem_iff t).2 h))]
    simp

theorem referenceTetrahedron_volume :
    volume.real referenceTetrahedron = physicalScale/6 := by
  rw [volume_slice_integral, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hpos] : -physicalScale/2 ≤ physicalScale/2)]
  let f : ℝ → ℝ := fun t => (1/2+t/physicalScale)*(1/2-t/physicalScale)
  have hs := intervalIntegral.mul_integral_comp_mul_left
    (a := -(1/2:ℝ)) (b := 1/2) (f := f) physicalScale
  have hl : physicalScale * (-(1/2:ℝ)) = -physicalScale/2 := by ring
  have hu : physicalScale * (1/2:ℝ) = physicalScale/2 := by ring
  rw [hl,hu] at hs
  change (∫ t in (-physicalScale/2)..(physicalScale/2), f t) = physicalScale/6
  rw [← hs]
  have he : (∫ t in (-(1/2:ℝ))..(1/2), f (physicalScale*t)) = (1/6:ℝ) := by
    have hp : (fun t => f (physicalScale*t)) = (fun t : ℝ => (1/4:ℝ)-t^2) := by
      funext t
      dsimp [f]
      rw [mul_div_cancel_left₀ _ hpos.ne']
      ring
    rw [hp, intervalIntegral.integral_sub (f := fun _ : ℝ => (1/4:ℝ))
      (g := fun t : ℝ => t^2) intervalIntegrable_const
      ((continuous_id.pow 2).intervalIntegrable _ _),
      intervalIntegral.integral_const, integral_pow]
    norm_num
  rw [he]
  ring

end RationalTetrahedron

namespace SlopeRational

theorem referenceTetrahedron_volume :
    volume.real referenceTetrahedron = physicalScale/6 :=
  RationalTetrahedron.referenceTetrahedron_volume

end SlopeRational

end

end OAI
