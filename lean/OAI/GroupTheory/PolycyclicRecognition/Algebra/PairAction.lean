import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactPairs
import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryProbability
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-!+# The normalized translation action on pairs

For a pair `(F,B)`, normalization of domain translation by `x` has forward
map `F(x)⁻¹ F(xz)` and inverse map `x⁻¹ B(F(x)z)`. These are actual maps,
with all Lipschitz and quasi-inverse bounds retained. Inverting the parameter
converts the manuscript's right action into a left action.
-/

noncomputable section

open scoped NNReal

namespace PolycyclicRecognition

open MeasureTheory

variable {G : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

/-- Normalize domain translation, on pairs of continuous maps. -/
def translatePair (x : G) (p : C(G, G) × C(G, G)) : C(G, G) × C(G, G) :=
  (⟨fun z => (p.1 x)⁻¹ * p.1 (x * z),
      continuous_const.mul (p.1.continuous.comp (continuous_const.mul continuous_id))⟩,
    ⟨fun z => x⁻¹ * p.2 (p.1 x * z),
      continuous_const.mul (p.2.continuous.comp (continuous_const.mul continuous_id))⟩)

omit [ProperSpace G] in
theorem translatePair_bounds_of_bounds (Λ : ℝ≥0) (p : C(G, G) × C(G, G))
    (hp : LipschitzPairBounds G Λ p) (x : G) :
    translatePair x p ∈ normalizedPairs G Λ := by
  obtain ⟨hF, hB, hlF, hlB, hBF, hFB⟩ := hp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist ((p.1 x)⁻¹ * p.1 (x * z))
      ((p.1 x)⁻¹ * p.1 (x * w)) ≤ _
    simpa only [dist_mul_left] using hF.dist_le_mul (x * z) (x * w)
  · apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (x⁻¹ * p.2 (p.1 x * z))
      (x⁻¹ * p.2 (p.1 x * w)) ≤ _
    simpa only [dist_mul_left] using
      hB.dist_le_mul (p.1 x * z) (p.1 x * w)
  · intro z w
    change _ ≤ dist ((p.1 x)⁻¹ * p.1 (x * z))
      ((p.1 x)⁻¹ * p.1 (x * w))
    simpa only [dist_mul_left] using hlF (x * z) (x * w)
  · intro z w
    change _ ≤ dist (x⁻¹ * p.2 (p.1 x * z))
      (x⁻¹ * p.2 (p.1 x * w))
    simpa only [dist_mul_left] using
      hlB (p.1 x * z) (p.1 x * w)
  · intro z
    change dist (x⁻¹ * p.2 (p.1 x * ((p.1 x)⁻¹ * p.1 (x * z)))) z ≤ Λ
    simp only [mul_inv_cancel_left]
    rw [← dist_mul_left x]
    simpa only [mul_inv_cancel_left] using hBF (x * z)
  · intro z
    change dist ((p.1 x)⁻¹ * p.1 (x * (x⁻¹ * p.2 (p.1 x * z)))) z ≤ Λ
    simp only [mul_inv_cancel_left]
    rw [← dist_mul_left (p.1 x)]
    simpa only [mul_inv_cancel_left] using hFB (p.1 x * z)
  · change (p.1 x)⁻¹ * p.1 (x * 1) = 1
    simp

omit [ProperSpace G] in
theorem translatePair_bounds (Λ : ℝ≥0) (p : NormalizedPair G Λ) (x : G) :
    translatePair x p.val ∈ normalizedPairs G Λ :=
  translatePair_bounds_of_bounds Λ p.val p.property.1 x

/-- Every pair satisfying the actual coarse bounds has a normalized representative. -/
def normalizePair {Λ : ℝ≥0} (p : C(G, G) × C(G, G))
    (hp : LipschitzPairBounds G Λ p) : NormalizedPair G Λ :=
  ⟨translatePair 1 p, translatePair_bounds_of_bounds Λ p hp 1⟩

/-- Translation as a map of the compact normalized section. -/
def normalizedTranslate {Λ : ℝ≥0} (x : G) (p : NormalizedPair G Λ) :
    NormalizedPair G Λ := ⟨translatePair x p.val, translatePair_bounds Λ p x⟩

omit [ProperSpace G] in
theorem normalizedTranslate_one {Λ : ℝ≥0} (p : NormalizedPair G Λ) :
    normalizedTranslate 1 p = p := by
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z
  · change (p.val.1 1)⁻¹ * p.val.1 (1 * z) = p.val.1 z
    simp [p.property.2]
  · change (1 : G)⁻¹ * p.val.2 (p.val.1 1 * z) = p.val.2 z
    simp [p.property.2]

omit [ProperSpace G] in
theorem normalizedTranslate_mul {Λ : ℝ≥0} (x y : G) (p : NormalizedPair G Λ) :
    normalizedTranslate y (normalizedTranslate x p) = normalizedTranslate (x * y) p := by
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z <;>
    simp [normalizedTranslate, translatePair, mul_assoc]

/-- The left action corresponding to normalized right translation. -/
instance normalizedPairAction (Λ : ℝ≥0) : MulAction G (NormalizedPair G Λ) where
  smul g p := normalizedTranslate g⁻¹ p
  one_smul p := by
    change normalizedTranslate (1 : G)⁻¹ p = p
    simpa only [inv_one] using normalizedTranslate_one p
  mul_smul g h p := by
    change normalizedTranslate (g * h)⁻¹ p =
      normalizedTranslate g⁻¹ (normalizedTranslate h⁻¹ p)
    rw [normalizedTranslate_mul, mul_inv_rev]

omit [ProperSpace G] in
@[simp] theorem normalizedPair_smul_fst {Λ : ℝ≥0} (g : G)
    (p : NormalizedPair G Λ) (z : G) :
    (g • p).val.1 z = (p.val.1 g⁻¹)⁻¹ * p.val.1 (g⁻¹ * z) := rfl

omit [ProperSpace G] in
@[simp] theorem normalizedPair_smul_snd {Λ : ℝ≥0} (g : G)
    (p : NormalizedPair G Λ) (z : G) :
    (g • p).val.2 z = g * p.val.2 (p.val.1 g⁻¹ * z) := by
  change g⁻¹⁻¹ * _ = _
  rw [inv_inv]

omit [IsIsometricSMul G G] in
theorem continuous_translatePair :
    Continuous (fun q : G × (C(G, G) × C(G, G)) => translatePair q.1 q.2) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      (q.1.2.1 q.1.1)⁻¹ * q.1.2.1 (q.1.1 * q.2))
    fun_prop
  · apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun q : (G × (C(G, G) × C(G, G))) × G =>
      q.1.1⁻¹ * q.1.2.2 (q.1.2.1 q.1.1 * q.2))
    fun_prop

instance normalizedPairContinuousAction (Λ : ℝ≥0) :
    ContinuousSMul G (NormalizedPair G Λ) where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact continuous_translatePair.comp
      (continuous_fst.inv.prodMk continuous_snd.subtype_val)

/-- The construction of the stationary probability applies to the actual
normalized pair action. -/
theorem exists_normalizedPair_probability (Λ : ℝ≥0)
    [Nonempty (NormalizedPair G Λ)]
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (M : ThompsonNonamenability.InvariantMean G) :
    ∃ μ : MeasureTheory.Measure (NormalizedPair G Λ),
      μ.Regular ∧ MeasureTheory.IsProbabilityMeasure μ ∧
        SMulInvariantMeasure G (NormalizedPair G Λ) μ := by
  exact exists_invariant_probability M

end PolycyclicRecognition

end

end OAI
