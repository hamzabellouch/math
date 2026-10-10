import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationarySlope
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ReducedCohomologyInput
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

namespace OAI

/-!
# The zero-mean Hilbert representation and stationary sublinearity

The closed kernel of integration is invariant under inverse pullback.
Ergodicity removes its invariant vectors. This constructs the representation
to which the published reduced-cohomology input is applied; the conclusion
is the manuscript's averaged sublinear estimate for a fixed measure.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory

variable {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]
  (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ]

attribute [local instance] stationaryL2Action

/-- The actual closed zero-mean subspace of `L²`. -/
abbrev ZeroMeanL2 : Submodule ℝ (Lp W 2 μ) := (stationaryL2Mean (W := W) μ).ker

/-- Constants have their stated mean on a probability space. -/
theorem stationaryL2Mean_const (w : W) : stationaryL2Mean μ (Lp.const 2 μ w) = w := by
  change (∫ x, (Lp.const 2 μ w) x ∂μ) = w
  rw [integral_congr_ae (Lp.coeFn_const 2 μ w)]
  simp

omit [NormedSpace ℝ W] [CompleteSpace W] in
/-- Constant functions are fixed by inverse pullback. -/
theorem stationaryPullback_const (g : G) (w : W) :
    stationaryPullback μ g (Lp.const 2 μ w) = Lp.const 2 μ w := by
  apply Lp.ext
  have h := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 μ w)
  exact (Lp.coeFn_compMeasurePreserving _ (measurePreserving_smul g⁻¹ μ)).trans
    (h.trans (Lp.coeFn_const 2 μ w).symm)

/-- Restrict the pullback representation to the kernel of integration. -/
@[instance_reducible]
def zeroMeanL2Action : DistribMulAction G (ZeroMeanL2 (W := W) μ) where
  smul g v := ⟨stationaryPullback μ g v.val, by
    change stationaryL2Mean μ (stationaryPullback μ g v.val) = 0
    rw [stationaryL2Mean_pullback]
    exact v.property⟩
  one_smul v := Subtype.ext (stationaryPullback_one (W := W) μ v.val)
  mul_smul g h v := Subtype.ext (stationaryPullback_mul (W := W) μ g h v.val)
  smul_zero g := Subtype.ext ((stationaryPullback (W := W) μ g).map_zero)
  smul_add g v w := Subtype.ext ((stationaryPullback (W := W) μ g).map_add v.val w.val)

attribute [local instance] zeroMeanL2Action

instance zeroMeanL2Isometric : IsIsometricSMul G (ZeroMeanL2 (W := W) μ) where
  isometry_smul g := by
    intro v w
    exact (Lp.isometry_compMeasurePreserving (measurePreserving_smul g⁻¹ μ)) v.val w.val

instance zeroMeanL2SMulComm : SMulCommClass G ℝ (ZeroMeanL2 (W := W) μ) where
  smul_comm g r v := Subtype.ext (smul_comm g r (v : Lp W 2 μ))

/-- Ergodicity removes every invariant vector from the zero-mean subspace. -/
theorem zeroMeanL2_no_fixed
    {G X W : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
    [MeasurableConstSMul G X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ]
    (v : ZeroMeanL2 (W := W) μ) (hfix : ∀ g : G, g • v = v) : v = 0 := by
  obtain ⟨w, hw⟩ := stationary_fixed_eq_const μ (v : Lp W 2 μ)
    (fun g => congrArg Subtype.val (hfix g))
  have hmean : stationaryL2Mean μ (v : Lp W 2 μ) = 0 := v.property
  rw [hw, stationaryL2Mean_const] at hmean
  apply Subtype.ext
  rw [hw, hmean, map_zero]
  rfl

/-- Averaging any `L²` cocycle gives a genuine height homomorphism. -/
def l2MeanSlope (b : G → Lp W 2 μ) (hb : IsCocycle b) : G →* Multiplicative W where
  toFun g := Multiplicative.ofAdd (stationaryL2Mean μ (b g))
  map_one' := by simp only [hb.map_one, map_zero]; rfl
  map_mul' g h := by
    apply Multiplicative.ext
    change stationaryL2Mean μ (b (g * h)) = _
    rw [hb g h, map_add]
    congr 1
    exact stationaryL2Mean_pullback μ g (b h)

/-- Subtracting the actual averaged slope produces a zero-mean cocycle. -/
def centeredL2Cocycle (b : G → Lp W 2 μ) (g : G) : ZeroMeanL2 (W := W) μ :=
  ⟨b g - Lp.const 2 μ (stationaryL2Mean μ (b g)), by
    change stationaryL2Mean μ (_ - _) = 0
    rw [map_sub, stationaryL2Mean_const, sub_self]⟩

theorem isCocycle_centeredL2 (b : G → Lp W 2 μ) (hb : IsCocycle b) :
    IsCocycle (centeredL2Cocycle μ b) := by
  intro g h
  apply Subtype.ext
  change b (g * h) - Lp.const 2 μ (stationaryL2Mean μ (b (g * h))) =
    (b g - Lp.const 2 μ (stationaryL2Mean μ (b g))) +
      stationaryPullback μ g (b h - Lp.const 2 μ (stationaryL2Mean μ (b h)))
  have hmean : stationaryL2Mean μ (g • b h) = stationaryL2Mean μ (b h) :=
    stationaryL2Mean_pullback μ g (b h)
  rw [hb g h, map_add, hmean, map_add,
    map_sub, stationaryPullback_const]
  rw [show g • b h = stationaryPullback μ g (b h) from rfl]
  abel

theorem continuous_centeredL2 {G : Type*} [Group G] [TopologicalSpace G]
    (b : G → Lp W 2 μ) (hb : Continuous b) : Continuous (centeredL2Cocycle μ b) := by
  exact (hb.sub ((Lp.constL 2 μ ℝ).continuous.comp
    ((stationaryL2Mean μ).continuous.comp hb))).subtype_mk _

/-- The fixed-measure stationary sublinear estimate, conditional only on the
precise reduced-cohomology input for the constructed zero-mean representation.
The analytic and algebraic hypotheses are verified on that representation. -/
theorem stationary_sublinear
    {G X W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [R1Space X]
    [MulAction G X] [ContinuousSMul G X]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul G X μ]
    [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (b : G → Lp W 2 μ) (hbcont : Continuous b) (hb : IsCocycle b)
    (Q : Set G) (hQ : IsCompact Q) (length : G → ℝ)
    (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ Q) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖b g - Lp.const 2 μ (l2MeanSlope μ b hb g).toAdd‖ ≤ ε * length g + B := by
  have hact (v : ZeroMeanL2 (W := W) μ) : Continuous (fun g : G => g • v) := by
    have h : Continuous (fun g : G => stationaryPullback μ g (v : Lp W 2 μ)) :=
      (continuous_stationaryPullback μ).comp (continuous_id.prodMk continuous_const)
    exact h.subtype_mk _
  exact sublinear_of_reducedCohomologyInput G (ZeroMeanL2 (W := W) μ) hvan
    (zeroMeanL2_no_fixed μ) hact (centeredL2Cocycle μ b)
    (continuous_centeredL2 μ b hbcont) (isCocycle_centeredL2 μ b hb)
    Q hQ length hlen ha hword

end PolycyclicRecognition

end

end OAI
