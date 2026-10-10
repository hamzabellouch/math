import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeH1
import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich

namespace OAI

/-! Actual compact localization on the planar Sobolev graph. Multiplication
by a compactly supported C¹ function is constructed on L² classes and their gradients,
then factored through the proved supported Rellich inclusion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Topology
namespace ContinuumCoulomb
namespace PlanarSobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance instLocalizationMeasurable : MeasurableSpace PlanarPosition := borel PlanarPosition
local instance instLocalizationBorel : BorelSpace PlanarPosition := ⟨rfl⟩
local instance instLocalizationMeasure : MeasureSpace PlanarPosition := measureSpaceOfInnerProductSpace

section LinearField
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure BoundedLinearField (F G : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  value : PlanarPosition → F →L[ℝ] G
  continuous : Continuous value
  bound : ℝ
  bound_spec : ∀ x, ‖value x‖ ≤ bound

theorem BoundedLinearField.memLp (A : BoundedLinearField F G)
    (u : Lp F 2 (volume : Measure PlanarPosition)) :
    MemLp (fun x => A.value x (u x)) 2 := by
  apply (Lp.memLp u).of_le_mul (c := A.bound)
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      A.continuous.aestronglyMeasurable (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall (fun x => (A.value x).le_opNorm (u x) |>.trans
    (mul_le_mul_of_nonneg_right (A.bound_spec x) (norm_nonneg _)))

def BoundedLinearField.applyLp (A : BoundedLinearField F G)
    (u : Lp F 2 (volume : Measure PlanarPosition)) : Lp G 2 (volume : Measure PlanarPosition) :=
  (A.memLp u).toLp (fun x => A.value x (u x))

theorem BoundedLinearField.applyLp_ae (A : BoundedLinearField F G)
    (u : Lp F 2 (volume : Measure PlanarPosition)) :
    A.applyLp u =ᵐ[volume] fun x => A.value x (u x) := (A.memLp u).coeFn_toLp

private def BoundedLinearField.linear (A : BoundedLinearField F G) :
    Lp F 2 (volume : Measure PlanarPosition) →ₗ[ℝ] Lp G 2 (volume : Measure PlanarPosition) where
  toFun := A.applyLp
  map_add' u v := by
    apply Lp.ext
    filter_upwards [A.applyLp_ae (u + v), A.applyLp_ae u, A.applyLp_ae v,
      Lp.coeFn_add u v, Lp.coeFn_add (A.applyLp u) (A.applyLp v)] with x h h₁ h₂ h₃ h₄
    simp only [h, h₄, h₃, Pi.add_apply, h₁, h₂, map_add]
  map_smul' c u := by
    apply Lp.ext
    change (A.applyLp (c • u) : PlanarPosition → G) =ᵐ[volume]
      (c • A.applyLp u : Lp G 2 volume)
    filter_upwards [A.applyLp_ae (c • u), A.applyLp_ae u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (A.applyLp u)] with x h h₁ h₂ h₃
    simp only [h, h₃, h₁, h₂, Pi.smul_apply, map_smul]

def BoundedLinearField.operator (A : BoundedLinearField F G) :
    Lp F 2 (volume : Measure PlanarPosition) →L[ℝ] Lp G 2 (volume : Measure PlanarPosition) :=
  A.linear.mkContinuous A.bound (fun u => Lp.norm_le_mul_norm_of_ae_le_mul (by
    filter_upwards [A.applyLp_ae u] with x hx
    change ‖A.applyLp u x‖ ≤ A.bound * ‖u x‖
    rw [hx]
    exact ((A.value x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (A.bound_spec x) (norm_nonneg _))))

end LinearField

private theorem test_norm_bounded (h : Test) : ∃ B : ℝ, ∀ x, ‖h.val x‖ ≤ B :=
  h.property.1.continuous.bounded_above_of_compact_support h.property.2

private theorem test_grad_bounded (h : Test) : ∃ B : ℝ, ∀ x, ‖grad h.val x‖ ≤ B :=
  (continuous_grad h.property.1).bounded_above_of_compact_support (hasCompactSupport_grad h.property.2)

def testNormBound (h : Test) : ℝ := Classical.choose (test_norm_bounded h)

theorem testNormBound_spec (h : Test) (x : PlanarPosition) : ‖h.val x‖ ≤ testNormBound h :=
  Classical.choose_spec (test_norm_bounded h) x

def testGradBound (h : Test) : ℝ := Classical.choose (test_grad_bounded h)

theorem testGradBound_spec (h : Test) (x : PlanarPosition) : ‖grad h.val x‖ ≤ testGradBound h :=
  Classical.choose_spec (test_grad_bounded h) x

def testScalarField (h : Test) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BoundedLinearField F F where
  value x := h.val x • ContinuousLinearMap.id ℝ F
  continuous := h.property.1.continuous.smul continuous_const
  bound := testNormBound h
  bound_spec x := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg (h.val x))).trans
      (by simpa only [mul_one] using testNormBound_spec h x)

def testGradientField (h : Test) : BoundedLinearField ℝ PlanarPosition where
  value x := ContinuousLinearMap.toSpanSingleton ℝ (grad h.val x)
  continuous := (ContinuousLinearMap.toSpanSingletonLIE ℝ PlanarPosition).continuous.comp
    (continuous_grad h.property.1)
  bound := testGradBound h
  bound_spec x := by
    rw [ContinuousLinearMap.norm_toSpanSingleton]
    exact testGradBound_spec h x

def testTargetMultiplier (h : Test) : Target →L[ℝ] Target :=
  ((testScalarField h ℝ).operator.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((testScalarField h PlanarPosition).operator.comp (ContinuousLinearMap.snd ℝ _ _)) +
      ((testGradientField h).operator.comp (ContinuousLinearMap.fst ℝ _ _)))

def testProduct (h u : Test) : Test := ⟨fun x => h.val x * u.val x,
  ⟨h.property.1.mul u.property.1, h.property.2.mul_right⟩⟩

theorem testProduct_grad (h u : Test) (x : PlanarPosition) :
    grad (testProduct h u).val x = h.val x • grad u.val x + u.val x • grad h.val x := by
  ext a
  rw [grad_coordinate]
  change planarPartial (fun y => h.val y * u.val y) (planarAxis a) x = _
  rw [planarPartial_mul _ _ h.property.1 u.property.1]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, grad_coordinate]

theorem testTargetMultiplier_graph (h u : Test) :
    testTargetMultiplier h (graph (μ := volume) u) = graph (μ := volume) (testProduct h u) := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(testScalarField h ℝ).applyLp_ae (toL2 (μ := volume) u),
      (memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      (memLp_of_mem_C1c (μ := volume) (testProduct h u).property).coeFn_toLp] with x hx hu hv
    change (testScalarField h ℝ).applyLp (toL2 (μ := volume) u) x =
      toL2 (μ := volume) (testProduct h u) x
    change toL2 (μ := volume) u x = u.val x at hu
    change toL2 (μ := volume) (testProduct h u) x = (testProduct h u).val x at hv
    rw [hx, hu, hv]
    rfl
  · apply Lp.ext
    filter_upwards [(testScalarField h PlanarPosition).applyLp_ae (toL2Grad (μ := volume) u),
      (testGradientField h).applyLp_ae (toL2 (μ := volume) u),
      Lp.coeFn_add ((testScalarField h PlanarPosition).applyLp (toL2Grad (μ := volume) u))
        ((testGradientField h).applyLp (toL2 (μ := volume) u)),
      (memLp_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      (memLp_grad_of_mem_C1c (μ := volume) u.property).coeFn_toLp,
      (memLp_grad_of_mem_C1c (μ := volume) (testProduct h u).property).coeFn_toLp]
      with x hx hx' hadd hu hg hv
    change (((testScalarField h PlanarPosition).applyLp (toL2Grad (μ := volume) u)) +
      (testGradientField h).applyLp (toL2 (μ := volume) u)) x = toL2Grad (μ := volume) (testProduct h u) x
    change toL2 (μ := volume) u x = u.val x at hu
    change toL2Grad (μ := volume) u x = grad u.val x at hg
    change toL2Grad (μ := volume) (testProduct h u) x = grad (testProduct h u).val x at hv
    rw [hadd]
    change (testScalarField h PlanarPosition).applyLp (toL2Grad (μ := volume) u) x +
      (testGradientField h).applyLp (toL2 (μ := volume) u) x = _
    rw [hx, hx', hu, hg, hv, testProduct_grad]
    rfl

theorem testTargetMultiplier_mem (h : Test) (u : Sobolev) : testTargetMultiplier h u.val ∈ Sobolev := by
  have hc : IsClosed {v : Target | testTargetMultiplier h v ∈ Sobolev} :=
    (isClosed_h1 (μ := volume) (E := PlanarPosition)).preimage (testTargetMultiplier h).continuous
  apply closure_minimal (s := (LinearMap.range (graph (μ := volume) (E := PlanarPosition)) : Set Target))
    (t := {v : Target | testTargetMultiplier h v ∈ Sobolev}) ?_ hc u.property
  rintro _ ⟨v, rfl⟩
  change testTargetMultiplier h (graph (μ := volume) v) ∈ Sobolev
  rw [testTargetMultiplier_graph]
  exact subset_closure ⟨testProduct h v, rfl⟩

def testSobolevMultiplier (h : Test) : Sobolev →L[ℝ] Sobolev :=
  ((testTargetMultiplier h).comp Sobolev.subtypeL).codRestrict Sobolev (testTargetMultiplier_mem h)

def testLocalizedL2 (h : Test) : Sobolev →L[ℝ] Lp ℝ 2 (volume : Measure PlanarPosition) :=
  (h1ToL2 (μ := volume) (E := PlanarPosition)).comp (testSobolevMultiplier h)

theorem testLocalizedL2_ae (h : Test) (u : Sobolev) :
    testLocalizedL2 h u =ᵐ[volume] fun x => h.val x * u.val.1 x := by
  exact (testScalarField h ℝ).applyLp_ae u.val.1

private theorem mem_extendByZero_range {K : Set PlanarPosition} (hK : MeasurableSet K)
    (f : Lp ℝ 2 (volume : Measure PlanarPosition))
    (hf : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    f ∈ LinearMap.range
      (Lp.extendByZeroₗᵢ (μ := volume) (E := ℝ) (p := 2) hK).toLinearMap := by
  let g : Lp ℝ 2 ((volume : Measure PlanarPosition).restrict K) :=
    ((Lp.memLp f).restrict K).toLp f
  have hg : ∀ᵐ x ∂volume, x ∈ K → g x = f x :=
    (ae_restrict_iff' hK).1 ((Lp.memLp f).restrict K).coeFn_toLp
  refine ⟨g, Lp.ext ?_⟩
  filter_upwards [Lp.extendByZeroₗᵢ_ae_eq hK g, hg, hf] with x he hgx hfx
  change Lp.extendByZeroₗᵢ hK g x = f x
  rw [he]
  by_cases hx : x ∈ K
  · simpa only [Set.indicator_of_mem hx] using hgx hx
  · simp only [Set.indicator_of_notMem hx, hfx hx]

theorem testSobolevMultiplier_supported (h : Test) (u : Sobolev) :
    testSobolevMultiplier h u ∈ h1On (tsupport h.val) (isClosed_tsupport h.val).measurableSet := by
  apply mem_extendByZero_range
  filter_upwards [testLocalizedL2_ae h u] with x hx
  intro hxs
  change testLocalizedL2 h u x = 0
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]

def testSupportedMultiplier (h : Test) :
    Sobolev →L[ℝ] h1On (tsupport h.val) (isClosed_tsupport h.val).measurableSet :=
  (testSobolevMultiplier h).codRestrict _ (testSobolevMultiplier_supported h)

theorem testLocalizedL2_compact (h : Test) : IsCompactOperator (testLocalizedL2 h) := by
  exact (isCompactOperator_h1OnToL2 h.property.2
    (isClosed_tsupport h.val).measurableSet).comp_clm (testSupportedMultiplier h)

def wellTest : Test := ⟨manufacturedPlanarWell,
  ⟨manufacturedPlanarWell_C7.of_le (by norm_num), manufacturedPlanarWell_hasCompactSupport⟩⟩

theorem wellTest_operator : (testScalarField wellTest ℝ).operator = wellMultiplier := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [(testScalarField wellTest ℝ).applyLp_ae u, wellMultiply_ae u] with x h₁ h₂
  change (testScalarField wellTest ℝ).applyLp u x = wellMultiply u x
  rw [h₁, h₂]
  rfl

theorem wellMultiplier_compact :
    IsCompactOperator (wellMultiplier.comp (h1ToL2 (μ := volume) (E := PlanarPosition))) := by
  have he : testLocalizedL2 wellTest =
      wellMultiplier.comp (h1ToL2 (μ := volume) (E := PlanarPosition)) := by
    apply ContinuousLinearMap.ext
    intro u
    change (testScalarField wellTest ℝ).operator u.val.1 = wellMultiplier u.val.1
    rw [wellTest_operator]
  rw [← he]
  exact testLocalizedL2_compact wellTest

end PlanarSobolev
end ContinuumCoulomb

end

end OAI
