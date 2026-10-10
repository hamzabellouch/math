import OAI.Analysis.CircleDomains.Probability.PublishedMeasureDuality
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace OAI

/-! Continuous test integrals on a compact family of finite measures and
the uniform positive mass needed for the compact duality construction. -/
open Set MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]

lemma compact_family_positive_mass {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S) :
    ∃ m : ℝ≥0, 0 < m ∧ ∀ v ∈ S, m ≤ v.mass := by
  obtain ⟨v,hv,hmin⟩ := hS.exists_isMinOn hne FiniteMeasure.continuous_mass.continuousOn
  refine ⟨v.mass,?_,hmin⟩
  exact pos_iff_ne_zero.mpr ((FiniteMeasure.mass_nonzero_iff v).mpr (fun he => hz (he ▸ hv)))

/-- The actual averaging operator used in compact-family separation. -/
def compactMeasureTestOperator (S : Set (FiniteMeasure Z)) :
    (Z →ᵇ ℝ) →ₗ[ℝ] C(S,ℝ) where
  toFun f := ⟨fun v => ∫ z, f z ∂(v.val : Measure Z),
    (FiniteMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_subtype_val⟩
  map_add' f g := by
    ext v
    exact integral_add (f.integrable (μ := (v.val : Measure Z)))
      (g.integrable (μ := (v.val : Measure Z)))
  map_smul' r f := by
    ext v
    exact integral_smul r f

lemma compactMeasureTestOperator_const (S : Set (FiniteMeasure Z)) (r : ℝ) (v : S) :
    compactMeasureTestOperator S (BoundedContinuousFunction.const Z r) v =
      r * (v.val.mass : ℝ) := by
  simp [compactMeasureTestOperator,integral_const,measureReal_def,
    ← FiniteMeasure.ennreal_mass,mul_comm]

lemma exists_compact_measure_constant_majorant {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (u : C(S,ℝ)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ v : S,
      u v ≤ compactMeasureTestOperator S (BoundedContinuousFunction.const Z r) v := by
  obtain ⟨m,hm,hmass⟩ := compact_family_positive_mass hS hne hz
  have hm' : 0 < (m : ℝ) := hm
  refine ⟨‖u‖ / m,div_nonneg (norm_nonneg _) hm'.le,?_⟩
  intro v
  rw [compactMeasureTestOperator_const]
  have hv : (m : ℝ) ≤ v.val.mass := hmass v.val v.property
  calc
    u v ≤ ‖u‖ := u.apply_le_norm v
    _ = (‖u‖ / m) * m := (div_mul_cancel₀ _ hm'.ne').symm
    _ ≤ (‖u‖ / m) * (v.val.mass : ℝ) :=
      mul_le_mul_of_nonneg_left hv (div_nonneg (norm_nonneg _) hm'.le)

end CircleDomainRigidity

end

end OAI
