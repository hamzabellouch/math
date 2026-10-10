import OAI.Analysis.CircleDomains.Sobolev.PeriodizedLevels
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

noncomputable def scalarLevelLength (D : Set ℂ) (f : ℂ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (μH[1] : Measure ℂ) (D ∩ {z | f z = t})

/-- Precisely the scalar planar coarea identity, including its required
Lebesgue measurability assertion. -/
def ScalarCoareaIdentity (D : Set ℂ) (f : ℂ → ℝ) : Prop :=
  AEMeasurable (scalarLevelLength D f) volume ∧
    (∫⁻ t, scalarLevelLength D f t) =
      ∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖

/-- Federer (1969), §3.2.11, specialized to a real
`C¹` function on an open subset of the Euclidean plane. -/
def PlanarScalarCoarea : Prop :=
  ∀ (D : Set ℂ), IsOpen D → ∀ (f : ℂ → ℝ), ContDiffOn ℝ 1 f D →
    ScalarCoareaIdentity D f

noncomputable def weightedScalarLevelLength (D : Set ℂ) (f : ℂ → ℝ)
    (q : ℂ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in D ∩ {z | f z = t}, q z ∂(μH[1] : Measure ℂ)

noncomputable def weightedCircleLevelLength (D : Set ℂ) (f : ℂ → ℝ)
    (q : ℂ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in D ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)},
    q z ∂(μH[1] : Measure ℂ)

/-- Precisely the nonnegative weighted scalar coarea formula. -/
def WeightedScalarCoareaIdentity (D : Set ℂ) (f : ℂ → ℝ)
    (q : ℂ → ℝ≥0∞) : Prop :=
  AEMeasurable (weightedScalarLevelLength D f q) volume ∧
    (∫⁻ t, weightedScalarLevelLength D f q t) =
      ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖

/-- Federer (1969), §3.2.12, the nonnegative weighted
coarea formula specialized to a scalar `C¹` function on a planar open
set. This is the identity used by `eq:weighted-level-bound` in §1 of the
Koebe manuscript. -/
def WeightedPlanarScalarCoarea : Prop :=
  ∀ (D : Set ℂ), IsOpen D → ∀ (f : ℂ → ℝ), ContDiffOn ℝ 1 f D →
    ∀ (q : ℂ → ℝ≥0∞), Measurable q → WeightedScalarCoareaIdentity D f q

theorem WeightedPlanarScalarCoarea.unweighted
    (hcoarea : WeightedPlanarScalarCoarea) : PlanarScalarCoarea := by
  intro D hD f hf
  have h := hcoarea D hD f hf (fun _ => 1) measurable_const
  have hfun : weightedScalarLevelLength D f (fun _ => 1) = scalarLevelLength D f := by
    funext t
    simp only [weightedScalarLevelLength, scalarLevelLength, lintegral_one,
      Measure.restrict_apply_univ]
  refine ⟨?_, ?_⟩
  · simpa only [hfun] using h.1
  · simpa only [hfun, one_mul] using h.2

/-- The scalar fibers are measurable even though the function is only
assumed continuous on its open domain. -/
theorem measurableSet_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (t : ℝ) :
    MeasurableSet (D ∩ {z | f z = t}) := by
  classical
  have hm : Measurable (D.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | f z = t} =
      D ∩ (D.piecewise f (fun _ => 0)) ⁻¹' {t} := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [heq]
  exact hD.measurableSet.inter (hm (measurableSet_singleton t))

/-- Countable additivity on the disjoint integer lifts is the exact
weighted circle-fiber identity. -/
theorem weightedCircleLevelLength_eq_periodized {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedCircleLevelLength D f q t =
      periodizedLevelLength (weightedScalarLevelLength D f q) t := by
  unfold weightedCircleLevelLength periodizedLevelLength weightedScalarLevelLength
  rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
  apply lintegral_iUnion (fun k : ℤ => measurableSet_scalar_level hD hf (t + (k : ℝ)))
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨_, hzi⟩ ⟨_, hzj⟩
  change f z = t + (i : ℝ) at hzi
  change f z = t + (j : ℝ) at hzj
  apply hij
  exact_mod_cast (show (i : ℝ) = (j : ℝ) by linarith)

theorem lintegral_periodizedLevelLength_of_aemeasurable
    (L : ℝ → ℝ≥0∞) (hL : AEMeasurable L volume) :
    (∫⁻ t in Ico (0 : ℝ) 1, periodizedLevelLength L t) = ∫⁻ t, L t := by
  have htranslate (k : ℤ) :
      ∀ᵐ t ∂volume, L (t + (k : ℝ)) = hL.mk L (t + (k : ℝ)) :=
    (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving.ae hL.ae_eq_mk
  have heq : periodizedLevelLength L =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      periodizedLevelLength (hL.mk L) := by
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr htranslate)] with t ht
    exact tsum_congr ht
  rw [lintegral_congr_ae heq, lintegral_periodizedLevelLength _ hL.measurable_mk,
    ← lintegral_congr_ae hL.ae_eq_mk]

/-- The weighted circle-valued coarea formula follows from the real
one, including the measurability needed for further integration. -/
theorem weighted_circle_coarea {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (q : ℂ → ℝ≥0∞)
    (hcoarea : WeightedScalarCoareaIdentity D f q) :
    AEMeasurable (weightedCircleLevelLength D f q)
        (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻ t in Ico (0 : ℝ) 1, weightedCircleLevelLength D f q t) =
        ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := by
  have heq : weightedCircleLevelLength D f q =
      periodizedLevelLength (weightedScalarLevelLength D f q) :=
    funext (weightedCircleLevelLength_eq_periodized hD hf q)
  rw [heq]
  constructor
  · apply AEMeasurable.restrict
    exact AEMeasurable.tsum (fun k : ℤ => hcoarea.1.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving)
  · rw [lintegral_periodizedLevelLength_of_aemeasurable _ hcoarea.1, hcoarea.2]

/-- The elementary finite-measure `L² → L¹` bound needed for coarea. -/
theorem lintegral_differentialNorm_le_area_add_energy (D : Set ℂ) (f : ℂ → ℝ) :
    (∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
      volume D + ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
  calc
    (∫⁻ z in D, ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
        ∫⁻ z in D, (1 + ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) := by
      apply lintegral_mono
      intro z
      calc
        ENNReal.ofReal ‖fderiv ℝ f z‖ ≤
            ENNReal.ofReal (1 + ‖fderiv ℝ f z‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (‖fderiv ℝ f z‖ - 1)]
        _ = 1 + ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by norm_num) (sq_nonneg _), ENNReal.ofReal_one]
    _ = volume D + ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
      rw [lintegral_add_left measurable_const, lintegral_one, Measure.restrict_apply_univ]

theorem scalar_coarea_integral_lt_top {D : Set ℂ} {f : ℂ → ℝ}
    (hcoarea : ScalarCoareaIdentity D f) (harea : volume D < ∞)
    (henergy : (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞) :
    (∫⁻ t, scalarLevelLength D f t) < ∞ := by
  rw [hcoarea.2]
  exact (lintegral_differentialNorm_le_area_add_energy D f).trans_lt
    (ENNReal.add_lt_top.mpr ⟨harea, henergy⟩)

/-- Square-integrability of the weight and differential controls their
product. Only finiteness is needed here, so the elementary quadratic
bound suffices. -/
theorem lintegral_weight_mul_differentialNorm_le_energies
    (D : Set ℂ) (f q : ℂ → ℝ) (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z) :
    (∫⁻ z in D, ENNReal.ofReal (q z) * ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
      (∫⁻ z in D, ENNReal.ofReal (q z ^ 2)) +
        ∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2) := by
  calc
    (∫⁻ z in D, ENNReal.ofReal (q z) * ENNReal.ofReal ‖fderiv ℝ f z‖) ≤
        ∫⁻ z in D,
          (ENNReal.ofReal (q z ^ 2) + ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) := by
      apply lintegral_mono
      intro z
      dsimp only
      rw [← ENNReal.ofReal_mul (hq0 z), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg (q z - ‖fderiv ℝ f z‖), sq_nonneg (q z),
        sq_nonneg ‖fderiv ℝ f z‖]
    _ = _ := lintegral_add_left (hq.pow_const 2).ennreal_ofReal _

/-- The weighted scalar coarea input gives the actual weighted circle
formula and almost-everywhere finite weighted length under the paper's
two `L²` assumptions. -/
theorem weighted_circle_coarea_of_finite_energy
    (hcoarea : WeightedPlanarScalarCoarea) {D : Set ℂ} (hD : IsOpen D)
    {f q : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z)
    (hq2 : (∫⁻ z in D, ENNReal.ofReal (q z ^ 2)) < ∞)
    (hf2 : (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞) :
    AEMeasurable (weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)))
        (volume.restrict (Ico (0 : ℝ) 1)) ∧
      (∫⁻ t in Ico (0 : ℝ) 1,
        weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t) =
        (∫⁻ z in D, ENNReal.ofReal (q z) * ENNReal.ofReal ‖fderiv ℝ f z‖) ∧
      (∫⁻ t in Ico (0 : ℝ) 1,
        weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t) < ∞ ∧
      ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) 1),
        weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t < ∞ := by
  obtain ⟨hmeas, heq⟩ := weighted_circle_coarea hD hf.continuousOn
    (fun z => ENNReal.ofReal (q z)) (hcoarea D hD f hf _ hq.ennreal_ofReal)
  have hfinite : (∫⁻ t in Ico (0 : ℝ) 1,
      weightedCircleLevelLength D f (fun z => ENNReal.ofReal (q z)) t) < ∞ := by
    rw [heq]
    exact (lintegral_weight_mul_differentialNorm_le_energies D f q hq hq0).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hq2, hf2⟩)
  exact ⟨hmeas, heq, hfinite, ae_lt_top' hmeas hfinite.ne⟩

/-- Periodization remains valid for Lebesgue measurable lengths. The
exceptional set and each of its integer translates are discarded
before summing the real-level lengths. -/
theorem ae_finite_hausdorffMeasure_scalar_mod_one_levels_of_aemeasurable
    {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (f : Z → ℝ) (D : Set Z) (L : ℝ → ℝ≥0∞) (hL : AEMeasurable L volume)
    (hfinite : (∫⁻ t, L t) < ∞)
    (hlength : ∀ t, (μH[1] : Measure Z) (D ∩ {z | f z = t}) ≤ L t) :
    ∀ᵐ (t : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1),
      (μH[1] : Measure Z) (D ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) < ∞ := by
  have hmkfinite : (∫⁻ t, hL.mk L t) < ∞ := by
    rwa [← lintegral_congr_ae hL.ae_eq_mk]
  have htranslate (k : ℤ) :
      ∀ᵐ t ∂volume, L (t + (k : ℝ)) = hL.mk L (t + (k : ℝ)) :=
    (measurePreserving_add_right volume (k : ℝ)).quasiMeasurePreserving.ae hL.ae_eq_mk
  have hall : ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) 1),
      ∀ k : ℤ, L (t + (k : ℝ)) = hL.mk L (t + (k : ℝ)) :=
    ae_restrict_of_ae (ae_all_iff.mpr htranslate)
  filter_upwards [ae_finite_periodizedLevelLength (hL.mk L) hL.measurable_mk hmkfinite,
    hall] with t ht heq
  apply lt_of_le_of_lt _ ht
  rw [unitAddCircle_level_inter_eq_iUnion_integer_levels]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => ?_)
  exact (hlength (t + (k : ℝ))).trans_eq (heq k)

/-- The finite physical length conclusion from the
coarea identity, finite area, and actual squared differential energy. -/
theorem ae_finite_planar_mod_one_levels {D : Set ℂ} {f : ℂ → ℝ}
    (hcoarea : ScalarCoareaIdentity D f) (harea : volume D < ∞)
    (henergy : (∫⁻ z in D, ENNReal.ofReal (‖fderiv ℝ f z‖ ^ 2)) < ∞) :
    ∀ᵐ (t : ℝ) ∂volume.restrict (Ico (0 : ℝ) 1),
      (μH[1] : Measure ℂ) (D ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) < ∞ :=
  ae_finite_hausdorffMeasure_scalar_mod_one_levels_of_aemeasurable f D
    (scalarLevelLength D f) hcoarea.1
    (scalar_coarea_integral_lt_top hcoarea harea henergy) (fun _ => le_rfl)

end CircleDomainRigidity

end OAI
