import OAI.Analysis.CircleDomains.Selection.TaggedPointContacts

namespace OAI

/-! Fubini for complete path images. At free points, tuple absolute
continuity reduces a path hit to a residual hit; residual nullity then
annihilates the integrated whole-image hit probability. -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def codeHitGraph (d : PathCodeData X Y) : Set (BasePathCode d × X) :=
  {q | q.2 ∈ Set.range q.1.val.1}

def codeResidualGraph (d : PathCodeData X Y) : Set (BasePathCode d × X) :=
  {q | q.2 ∈ residualImage d.dust q.1.val}

theorem isClosed_codeHitGraph (d : PathCodeData X Y) : IsClosed (codeHitGraph d) :=
  isClosed_pathHitSet.preimage
    (((continuous_subtype_val.comp continuous_fst).fst).prodMk continuous_snd)

theorem isClosed_codeResidualGraph (d : PathCodeData X Y) (hB : IsClosed d.dust) :
    IsClosed (codeResidualGraph d) :=
  (isClosed_residualImageGraph hB).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

def codeHitProbability (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (x : X) : ℝ≥0∞ :=
  (P : Measure (BasePathCode d)) {Γ | x ∈ Set.range Γ.val.1}

def codeResidualProbability (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (x : X) : ℝ≥0∞ :=
  (P : Measure (BasePathCode d)) {Γ | x ∈ residualImage d.dust Γ.val}

variable [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X]

theorem measurable_codeHitProbability (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) : Measurable (codeHitProbability d P) :=
  measurable_measure_prodMk_right (isClosed_codeHitGraph d).measurableSet

theorem measurable_codeResidualProbability (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (P : ProbabilityMeasure (BasePathCode d)) : Measurable (codeResidualProbability d P) :=
  measurable_measure_prodMk_right (isClosed_codeResidualGraph d hB).measurableSet

theorem lintegral_codeResidualProbability (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (P : ProbabilityMeasure (BasePathCode d)) (ν : Measure X) [SFinite ν] :
    ∫⁻ x, codeResidualProbability d P x ∂ν =
      ∫⁻ Γ : BasePathCode d, ν (residualImage d.dust Γ.val) ∂(P : Measure (BasePathCode d)) := by
  have hm := (isClosed_codeResidualGraph d hB).measurableSet
  exact (Measure.prod_apply_symm hm).symm.trans (Measure.prod_apply hm)

omit [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X] in
theorem codeHitProbability_eq_residual (d : PathCodeData X Y)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    {x : X} (hx : x ∈ d.dust)
    (hfree : ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0) :
    codeHitProbability d P x = codeResidualProbability d P x := by
  apply measure_congr
  filter_upwards [ae_path_hit_iff_residual d hH P ω hτ hx hfree] with Γ hΓ
  exact propext hΓ

theorem lintegral_codeHitProbability_zero (d : PathCodeData X Y) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i)) (P : ProbabilityMeasure (BasePathCode d))
    (ω : TupleType → ℝ≥0∞) (hτ : meanCodeTuple d P ≪ tupleReference ω)
    (ν : Measure X) [SFinite ν]
    (hfree : ∀ᵐ x ∂ν, x ∈ d.dust ∧
      ∀ i, volume {t : UnitAddCircle | (t, x) ∈ d.levels i} = 0)
    (hres : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) :
    ∫⁻ x, codeHitProbability d P x ∂ν = 0 := by
  calc
    _ = ∫⁻ x, codeResidualProbability d P x ∂ν :=
      lintegral_congr_ae (hfree.mono fun x hx =>
        codeHitProbability_eq_residual d hH P ω hτ hx.1 hx.2)
    _ = ∫⁻ Γ : BasePathCode d, ν (residualImage d.dust Γ.val)
        ∂(P : Measure (BasePathCode d)) := lintegral_codeResidualProbability d hB P ν
    _ = 0 := (lintegral_eq_zero_iff
      ((measurable_residualImageMass hB ν).comp measurable_subtype_coe)).mpr hres

end CircleDomainRigidity

end

end OAI
