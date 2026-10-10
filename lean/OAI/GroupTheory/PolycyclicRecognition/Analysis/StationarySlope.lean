import OAI.GroupTheory.PolycyclicRecognition.Algebra.CocycleGrowth
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Function

namespace OAI

/-!
# Averaging the stationary height cocycle

The normalized pair space carries a measure-preserving action. Its height
evaluation is a cocycle for inverse pullback. We construct that action on the
actual space `L²`, and show that integration gives an additive slope. No
reduced-cohomology assertion is assumed in this construction.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X]
  [NormedAddCommGroup W]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- Inverse pullback is the left representation associated to a left action. -/
def stationaryPullback (g : G) : Lp W 2 μ →+ Lp W 2 μ :=
  Lp.compMeasurePreserving (fun x : X => g⁻¹ • x) (measurePreserving_smul g⁻¹ μ)

theorem stationaryPullback_one (v : Lp W 2 μ) : stationaryPullback μ (1 : G) v = v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v (measurePreserving_smul (1 : G)⁻¹ μ)]
    with x hx
  exact hx.trans (by simp)

theorem stationaryPullback_mul (g h : G) (v : Lp W 2 μ) :
    stationaryPullback μ (g * h) v =
      stationaryPullback μ g (stationaryPullback μ h v) := by
  simpa only [stationaryPullback, mul_inv_rev, mul_smul, Function.comp_def] using
    Lp.compMeasurePreserving_comp_apply v (measurePreserving_smul h⁻¹ μ)
      (measurePreserving_smul g⁻¹ μ)

/-- The isometric additive action on the genuine `L²` space. -/
@[instance_reducible]
def stationaryL2Action : DistribMulAction G (Lp W 2 μ) where
  smul g v := stationaryPullback μ g v
  one_smul := stationaryPullback_one μ
  mul_smul := stationaryPullback_mul μ
  smul_zero g := (stationaryPullback (W := W) μ g).map_zero
  smul_add g x y := (stationaryPullback (W := W) μ g).map_add x y

attribute [local instance] stationaryL2Action

/-- Constants are invariant for a finite invariant measure, without a
probability normalization. -/
theorem stationaryPullback_const_finite [IsFiniteMeasure μ] (g : G) (w : W) :
    stationaryPullback μ g (Lp.const 2 μ w) = Lp.const 2 μ w := by
  apply Lp.ext
  have h := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 μ w)
  exact (Lp.coeFn_compMeasurePreserving _ (measurePreserving_smul g⁻¹ μ)).trans
    (h.trans (Lp.coeFn_const 2 μ w).symm)

instance stationaryL2Isometric : IsIsometricSMul G (Lp W 2 μ) where
  isometry_smul g := by
    change Isometry (stationaryPullback (W := W) μ g)
    exact Lp.isometry_compMeasurePreserving (measurePreserving_smul g⁻¹ μ)

section ContinuousAction

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [BorelSpace X] [R1Space X]
  [ContinuousSMul G X] [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ]

/-- Strong continuity follows from the actual continuous action on the
underlying measure space and density of simple functions in `L²`. -/
theorem continuous_stationaryPullback :
    Continuous (fun z : G × Lp W 2 μ => stationaryPullback μ z.1 z.2) := by
  let T : G × Lp W 2 μ → C(X, X) := fun z =>
    ⟨fun x => z.1⁻¹ • x, continuous_const_smul _⟩
  have hT : Continuous T := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.fst.inv).smul continuous_snd
  exact continuous_snd.compMeasurePreservingLp hT
    (fun z => measurePreserving_smul z.1⁻¹ μ) (by norm_num)

end ContinuousAction

/-- Pointwise measurable height cocycles give `L²` cocycles without selecting
pointwise representatives of the resulting equivalence classes. -/
theorem isCocycle_toL2 (b : G → X → W) (hb : ∀ g, MemLp (b g) 2 μ)
    (hc : ∀ g h x, b (g * h) x = b g x + b h (g⁻¹ • x)) :
    IsCocycle (fun g => (hb g).toLp (b g)) := by
  intro g h
  change (hb (g * h)).toLp (b (g * h)) =
    (hb g).toLp (b g) + stationaryPullback μ g ((hb h).toLp (b h))
  rw [stationaryPullback, Lp.toLp_compMeasurePreserving]
  rw [← MemLp.toLp_add]
  apply Lp.ext
  filter_upwards [(hb (g * h)).coeFn_toLp,
    ((hb g).add ((hb h).comp_measurePreserving (measurePreserving_smul g⁻¹ μ))).coeFn_toLp]
    with x hx hy
  rw [hx, hy]
  exact hc g h x

variable [NormedSpace ℝ W] [CompleteSpace W]

instance stationaryL2SMulComm : SMulCommClass G ℝ (Lp W 2 μ) where
  smul_comm g r v := (Lp.compMeasurePreservingₗ ℝ
    (fun x : X => g⁻¹ • x) (measurePreserving_smul g⁻¹ μ)).map_smul r v

omit [CompleteSpace W] in
/-- The averaging operator is bounded by one on a probability space. -/
theorem norm_integral_le_l2 [IsProbabilityMeasure μ] (v : Lp W 2 μ) :
    ‖∫ x, v x ∂μ‖ ≤ ‖v‖ := by
  calc
    ‖∫ x, v x ∂μ‖ ≤ (∫⁻ x, ENNReal.ofReal ‖v x‖ ∂μ).toReal :=
      norm_integral_le_lintegral_norm _
    _ = (eLpNorm v 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable v)]
      simp only [ofReal_norm]
    _ ≤ (eLpNorm v 2 μ).toReal := ENNReal.toReal_mono (Lp.eLpNorm_ne_top v)
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    _ = ‖v‖ := rfl

/-- Averaging as an actual bounded linear operator on `L²`. -/
def stationaryL2Mean [IsProbabilityMeasure μ] : Lp W 2 μ →L[ℝ] W :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x, v x ∂μ
      map_add' := fun v w => by
        calc
          (∫ x, (v + w) x ∂μ) = ∫ x, v x + w x ∂μ := integral_congr_ae (Lp.coeFn_add v w)
          _ = _ := integral_add ((Lp.memLp v).integrable (by norm_num))
            ((Lp.memLp w).integrable (by norm_num))
      map_smul' := fun r v => by
        calc
          (∫ x, (r • v) x ∂μ) = ∫ x, r • v x ∂μ := integral_congr_ae (Lp.coeFn_smul r v)
          _ = _ := integral_smul r _ }
    1 (fun v => by change ‖∫ x, v x ∂μ‖ ≤ 1 * ‖v‖; simpa using norm_integral_le_l2 μ v)

omit [CompleteSpace W] in
/-- The mean is invariant under the pullback representation. -/
theorem stationaryL2Mean_pullback [IsProbabilityMeasure μ] (g : G) (v : Lp W 2 μ) :
    stationaryL2Mean μ (stationaryPullback μ g v) = stationaryL2Mean μ v := by
  change (∫ x, (stationaryPullback μ g v) x ∂μ) = ∫ x, v x ∂μ
  calc
    (∫ x, (stationaryPullback μ g v) x ∂μ) = ∫ x, v (g⁻¹ • x) ∂μ :=
      integral_congr_ae (Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g⁻¹ μ))
    _ = _ := (measurePreserving_smul g⁻¹ μ).integral_comp
      (measurableEmbedding_const_smul g⁻¹) _

/-- The average is a genuine homomorphism; invariance removes the translated
second summand in the cocycle equation. -/
def stationaryMean (b : G → X → W) (hb : ∀ g, Integrable (b g) μ)
    (hc : ∀ g h x, b (g * h) x = b g x + b h (g⁻¹ • x)) :
    G →* Multiplicative W where
  toFun g := Multiplicative.ofAdd (∫ x, b g x ∂μ)
  map_one' := by
    have hz : b 1 = 0 := by
      funext x
      simpa using (hc 1 1 x).symm
    simp [hz]
  map_mul' g h := by
    apply Multiplicative.ext
    change (∫ x, b (g * h) x ∂μ) = (∫ x, b g x ∂μ) + ∫ x, b h x ∂μ
    have hi : Integrable (fun x => b h (g⁻¹ • x)) μ :=
      (measurePreserving_smul g⁻¹ μ).integrable_comp_of_integrable (hb h)
    simp_rw [hc g h]
    rw [integral_add (hb g) hi]
    congr 1
    exact (measurePreserving_smul g⁻¹ μ).integral_comp
      (measurableEmbedding_const_smul g⁻¹) (b h)

/-- On a probability space the centered pointwise cocycle has zero mean. -/
theorem integral_centered_stationaryMean [IsProbabilityMeasure μ]
    (b : G → X → W) (hb : ∀ g, Integrable (b g) μ)
    (hc : ∀ g h x, b (g * h) x = b g x + b h (g⁻¹ • x)) (g : G) :
    (∫ x, b g x - (stationaryMean μ b hb hc g).toAdd ∂μ) = 0 := by
  rw [integral_sub (hb g) (integrable_const _), integral_const]
  simp [stationaryMean]

/-- Ergodicity of the action, rather than an assumption about its Hilbert
representation, identifies all invariant `L²` vectors with constants. -/
theorem stationary_fixed_eq_const
    {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
    [MeasurableConstSMul G X] [NormedAddCommGroup W] [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ] (v : Lp W 2 μ)
    (hfix : ∀ g : G, stationaryPullback μ g v = v) :
    ∃ c : W, v = Lp.const 2 μ c := by
  borelize W
  have hc : ∃ c : W, (v : X → W) =ᵐ[μ] Function.const X c := by
    apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
    intro U hU
    apply eventuallyEmptyOrUniv_iff.mp
    apply aeconst_of_forall_preimage_smul_ae_eq G
      ((Lp.aestronglyMeasurable v).aemeasurable.nullMeasurable hU)
    intro g
    have heq : Lp.compMeasurePreserving (fun x : X => g • x)
        (measurePreserving_smul g μ) v = v := by
      simpa only [stationaryPullback, inv_inv] using hfix g⁻¹
    have hae := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g μ)
    rw [heq] at hae
    filter_upwards [hae] with x hx
    apply propext
    change (v (g • x) ∈ U ↔ v x ∈ U)
    rw [hx]
    rfl
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, Lp.ext (hc.trans (Lp.coeFn_const 2 μ c).symm)⟩

end PolycyclicRecognition

end

end OAI
