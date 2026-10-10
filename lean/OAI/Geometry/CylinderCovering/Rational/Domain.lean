import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions

namespace OAI

open Set MeasureTheory

noncomputable section

namespace SlopeRational

lemma ceilingPolynomial_continuous (d : ℝ) : Continuous (ceilingPolynomial d) := by
  unfold ceilingPolynomial ceilingCoefficient
  fun_prop

lemma labelDomain_bounds {d ε q : ℝ} {z : Plane} (hz : z ∈ labelDomain d ε q) :
    -(1 / 4 : ℝ) ≤ z 1 ∧ z 1 ≤ 1 / 2 ∧ |z 0| ≤ 3 / 8 := by
  rcases hz with ⟨hw, hfloor, hceil⟩
  change 2 * |z 0| ≤ 1 / 2 - z 1 at hw
  exact ⟨hfloor, by linarith [abs_nonneg (z 0)], by linarith⟩

lemma wedge_isClosed : IsClosed wedge := by
  unfold wedge radius
  exact isClosed_le (by fun_prop) (by fun_prop)

lemma labelDomain_isClosed (d ε q : ℝ) : IsClosed (labelDomain d ε q) := by
  unfold labelDomain
  exact wedge_isClosed.inter ((isClosed_le
    (f := fun _ : Plane => -(1 / 4 : ℝ)) (g := fun z => z 1)
    (by fun_prop) (by fun_prop)).inter
    (isClosed_le (f := fun z : Plane => -ε ^ 2 * ceilingPolynomial d (z 0) - q)
      (g := fun z => z 1)
      (by unfold ceilingPolynomial ceilingCoefficient; fun_prop) (by fun_prop)))

lemma labelDomain_isCompact (d ε q : ℝ) : IsCompact (labelDomain d ε q) := by
  have hbox : IsCompact ((fun p : ℝ × ℝ => vec2 p.1 p.2) ''
      (Icc (-(3 / 8 : ℝ)) (3 / 8) ×ˢ Icc (-(1 / 4 : ℝ)) (1 / 2))) :=
    (isCompact_Icc.prod isCompact_Icc).image (by unfold vec2; fun_prop)
  apply hbox.of_isClosed_subset (labelDomain_isClosed d ε q)
  intro z hz
  obtain ⟨hl, hu, hy⟩ := labelDomain_bounds hz
  refine ⟨(z 0, z 1), ⟨abs_le.mp hy, hl, hu⟩, ?_⟩
  ext i
  fin_cases i <;> simp [vec2]

lemma labelDomain_measurableSet (d ε q : ℝ) : MeasurableSet (labelDomain d ε q) :=
  (labelDomain_isClosed d ε q).measurableSet

lemma labelDomain_mem_iff (d ε q : ℝ) (z : Plane) :
    z ∈ labelDomain d ε q ↔
      z 1 ∈ Icc (max (-(1 / 4 : ℝ))
        (-ε ^ 2 * ceilingPolynomial d (z 0) - q)) (1 / 2 - 2 * |z 0|) := by
  simp only [labelDomain, wedge, radius, mem_ofPred_eq, mem_Icc, max_le_iff]
  constructor
  · rintro ⟨hw, hl, hp⟩
    exact ⟨⟨hl, hp⟩, by linarith⟩
  · rintro ⟨⟨hl, hp⟩, hw⟩
    exact ⟨by linarith, hl, hp⟩

lemma labelDomain_vertical_section (d ε q y : ℝ) :
    {t : ℝ | vec2 y t ∈ labelDomain d ε q} =
      Icc (max (-(1 / 4 : ℝ)) (-ε ^ 2 * ceilingPolynomial d y - q))
        (1 / 2 - 2 * |y|) := by
  ext t
  simpa [vec2] using labelDomain_mem_iff d ε q (vec2 y t)

lemma labelDomain_volume_ne_top (d ε q : ℝ) :
    volume (labelDomain d ε q) ≠ ⊤ :=
  (labelDomain_isCompact d ε q).measure_lt_top.ne

namespace DomainGeometry

def pairEquiv : (ℝ × ℝ) ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma pairEquiv_measurePreserving : MeasurePreserving pairEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma volume_graph_eq_zero {f : ℝ → ℝ} (hf : Continuous f) :
    volume {z : Plane | z 1 = f (z 0)} = 0 := by
  have hs : MeasurableSet {z : Plane | z 1 = f (z 0)} :=
    (isClosed_eq (by fun_prop) (hf.comp (by fun_prop))).measurableSet
  rw [← pairEquiv_measurePreserving.measure_preimage hs.nullMeasurableSet, Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null (hs.preimage pairEquiv.measurable)
  filter_upwards with y
  have heq : Prod.mk y ⁻¹' (pairEquiv ⁻¹' {z : Plane | z 1 = f (z 0)}) =
      {f y} := by
    ext t
    simp [pairEquiv, MeasurableEquiv.finTwoArrow]
  rw [heq]
  exact measure_singleton (f y)

end DomainGeometry

lemma frontier_labelDomain_subset (d ε q : ℝ) :
    frontier (labelDomain d ε q) ⊆
      {z : Plane | z 1 = 1 / 2 - 2 * |z 0|} ∪
      ({z : Plane | z 1 = -(1 / 4 : ℝ)} ∪
       {z : Plane | z 1 = -ε ^ 2 * ceilingPolynomial d (z 0) - q}) := by
  intro z hz
  change z ∈ frontier (wedge ∩
    ({w : Plane | -(1 / 4 : ℝ) ≤ w 1} ∩
     {w : Plane | -ε ^ 2 * ceilingPolynomial d (w 0) - q ≤ w 1})) at hz
  rcases frontier_inter_subset _ _ hz with hw | hr
  · left
    have he := frontier_le_subset_eq
      (f := fun w : Plane => 2 * |w 0|)
      (g := fun w : Plane => 1 / 2 - w 1)
      (by fun_prop) (by fun_prop) hw.1
    change 2 * |z 0| = 1 / 2 - z 1 at he
    change z 1 = 1 / 2 - 2 * |z 0|
    linarith
  · right
    rcases frontier_inter_subset _ _ hr.2 with hf | hp
    · left
      exact (frontier_le_subset_eq
        (f := fun _ : Plane => -(1 / 4 : ℝ)) (g := fun w => w 1)
        (by fun_prop) (by fun_prop) hf.1).symm
    · right
      exact (frontier_le_subset_eq
        (f := fun w : Plane => -ε ^ 2 * ceilingPolynomial d (w 0) - q)
        (g := fun w => w 1)
        (by unfold ceilingPolynomial ceilingCoefficient; fun_prop)
        (by fun_prop) hp.2).symm

lemma volume_frontier_labelDomain (d ε q : ℝ) :
    volume (frontier (labelDomain d ε q)) = 0 := by
  apply measure_mono_null (frontier_labelDomain_subset d ε q)
  apply measure_union_null
  · exact DomainGeometry.volume_graph_eq_zero (f := fun y => 1 / 2 - 2 * |y|) (by fun_prop)
  · apply measure_union_null
    · exact DomainGeometry.volume_graph_eq_zero (f := fun _ => -(1 / 4 : ℝ)) continuous_const
    · exact DomainGeometry.volume_graph_eq_zero
        (f := fun y => -ε ^ 2 * ceilingPolynomial d y - q)
        (by unfold ceilingPolynomial ceilingCoefficient; fun_prop)

lemma labelDomain_volume_le (d ε q : ℝ) :
    volume (labelDomain d ε q) ≤ ENNReal.ofReal (9 / 16 : ℝ) := by
  rw [← DomainGeometry.pairEquiv_measurePreserving.measure_preimage
    (labelDomain_measurableSet d ε q).nullMeasurableSet, Measure.volume_eq_prod]
  calc
    (volume.prod volume) (DomainGeometry.pairEquiv ⁻¹' labelDomain d ε q) ≤
        (volume.prod volume)
          (Icc (-(3 / 8 : ℝ)) (3 / 8) ×ˢ Icc (-(1 / 4 : ℝ)) (1 / 2)) := by
      apply measure_mono
      intro p hp
      have hz := labelDomain_bounds hp
      change -(1 / 4 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 / 2 ∧ |p.1| ≤ 3 / 8 at hz
      exact ⟨abs_le.mp hz.2.2, hz.1, hz.2.1⟩
    _ = ENNReal.ofReal (9 / 16 : ℝ) := by
      rw [Measure.prod_prod]
      norm_num [Real.volume_Icc]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      norm_num

lemma labelDomain_realVolume_le (d ε q : ℝ) :
    volume.real (labelDomain d ε q) ≤ 9 / 16 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (labelDomain_volume_le d ε q)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 9 / 16)] using h

end SlopeRational

end

end OAI
