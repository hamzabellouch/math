import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalDomain
import OAI.MeasureTheory.Falconer.Graphs.GraphGlobalSupports

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def graphTransport (F : ℝ → UnitCircle → UnitCircle → ℂ)
    (Ψ : ℝ → ℝ) (R axis : ℝ) (p : ℝ × Plane) : ℂ :=
  (‖p.2‖*Real.sqrt (1+p.1^2))⁻¹ •
    (Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) •
      F (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2))
        (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1))
        (sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)))

def graphTransportBox : Set (ℝ × Plane) := Icc (-4) 4 ×ˢ Metric.closedBall 0 8

theorem graphTransportBox_compact : IsCompact graphTransportBox :=
  isCompact_Icc.prod (isCompact_closedBall 0 8)

theorem graphPlaneAngle_measurable : Measurable graphPlaneAngle := by
  change Measurable (fun η => Complex.arg (Complex.equivRealProd.symm (graphPlaneEquiv.symm η)))
  exact Complex.measurable_arg.comp
    (Complex.measurableEquivRealProd.symm.measurable.comp graphPlaneEquiv.symm.measurable)

theorem graphTransport_measurable {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (R axis : ℝ) :
    Measurable (graphTransport F Ψ R axis) := by
  have ha : Measurable (fun p : ℝ × Plane => graphPlaneAngle p.2) :=
    graphPlaneAngle_measurable.comp measurable_snd
  have hu : Measurable (fun p : ℝ × Plane =>
      sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1)) := by fun_prop
  have hv : Measurable (fun p : ℝ × Plane =>
      sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)) := by fun_prop
  unfold graphTransport
  simp only [Complex.real_smul]
  apply Measurable.mul
  · fun_prop
  · apply Measurable.mul
    · apply Complex.measurable_ofReal.comp
      exact hΨ.comp (show Measurable (fun p : ℝ × Plane =>
        ‖p.2‖*Real.sqrt (1+p.1^2)/2) from by fun_prop)
    · exact hF.comp (show Measurable (fun p : ℝ × Plane =>
        (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2),
          (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1),
           sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)))) from
        (by fun_prop))

theorem graphTransport_support {F : ℝ → UnitCircle → UnitCircle → ℂ}
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (R axis : ℝ)
    (hchart : ∀ r φ z, F r (sourceUnitDirection (φ+Real.arctan z))
      (sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    Function.support (graphTransport F Ψ R axis) ⊆ graphTransportBox := by
  intro p hp
  have hb : Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hf : F (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2))
      (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1))
      (sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+axis)) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hr := hsupp _ hb
  have hz := hchart _ _ _ hf
  have hs : 1 ≤ Real.sqrt (1+p.1^2) :=
    Real.one_le_sqrt.mpr (le_add_of_nonneg_right (sq_nonneg p.1))
  refine ⟨abs_le.mp hz, ?_⟩
  change dist p.2 0 ≤ 8
  rw [dist_zero_right]
  nlinarith [hr.2, mul_le_mul_of_nonneg_left hs (norm_nonneg p.2)]

theorem graphTransport_norm_le {F : ℝ → UnitCircle → UnitCircle → ℂ}
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF : ∀ r u v, ‖F r u v‖ ≤ C) (hΨ : ∀ t, |Ψ t| ≤ B)
    (R axis : ℝ) (p : ℝ × Plane) : ‖graphTransport F Ψ R axis p‖ ≤ 2*(B*C) := by
  by_cases hz : Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) = 0
  · simp [graphTransport, hz, mul_nonneg hB hC]
  have hr := (hsupp _ hz).1
  have hd : (0:ℝ) < ‖p.2‖*Real.sqrt (1+p.1^2) := by linarith
  have hi : (‖p.2‖*Real.sqrt (1+p.1^2))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    linarith
  simp only [graphTransport, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hd]
  exact mul_le_mul hi (mul_le_mul (hΨ _) (hF _ _ _) (norm_nonneg _) hB)
    (by positivity) (by norm_num)

theorem graphTransport_integrable {F : ℝ → UnitCircle → UnitCircle → ℂ}
    (hF : Measurable (fun p : ℝ × (UnitCircle × UnitCircle) => F p.1 p.2.1 p.2.2))
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hbound : ∀ r u v, ‖F r u v‖ ≤ C) (hbump : ∀ t, |Ψ t| ≤ B)
    (R axis : ℝ)
    (hchart : ∀ r φ z, F r (sourceUnitDirection (φ+Real.arctan z))
      (sourceUnitDirection (φ-Real.arctan z+axis)) ≠ 0 → |z| ≤ 4) :
    Integrable (graphTransport F Ψ R axis) := by
  apply (integrableOn_iff_integrable_of_support_subset
    (graphTransport_support hsupp R axis hchart)).mp
  exact IntegrableOn.of_bound graphTransportBox_compact.measure_lt_top
    (graphTransport_measurable hF hΨ R axis).aestronglyMeasurable
    (2*(B*C)) (Filter.Eventually.of_forall (graphTransport_norm_le hsupp hC hB hbound hbump R axis))

theorem graphTransport_annulus_integral (F : ℝ → UnitCircle → UnitCircle → ℂ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (R axis z : ℝ) :
    (∫ η in graphGlobalAnnulus (1/4) 4 z, graphTransport F Ψ R axis (z,η)) =
      ∫ η, graphTransport F Ψ R axis (z,η) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro η hη
  have hz : Ψ (‖η‖*Real.sqrt (1+z^2)/2) = 0 := by
    by_contra hn
    exact hη (hsupp _ hn)
  simp [graphTransport, hz]

end PlanarFalconer

end OAI
