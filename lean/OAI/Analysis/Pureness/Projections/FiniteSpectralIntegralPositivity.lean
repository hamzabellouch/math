import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralBounds
import OAI.Analysis.Pureness.Divisibility.FiniteLscComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set OrderedSemigroup
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteSpectralIntegral_cut_lower_bound
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (ε : ℝ≥0) :
    d (finitePositiveClass n (Positive.cut ε M)) * (ε : ℝ≥0∞) ≤ finiteSpectralIntegral d n M := by
  rw [← ENNReal.ofReal_coe_nnreal,← positive_halfline_indicator_integral]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases htε : t < ε
  · rw [Set.indicator_of_mem (show t ∈ Iio (ε : ℝ) from htε)]
    have hle : t.toNNReal ≤ ε := by
      change (t.toNNReal : ℝ) ≤ ε
      rw [Real.coe_toNNReal t (le_of_lt ht)]
      exact htε.le
    exact finiteCutValue_antitone d hd n M hle
  · rw [Set.indicator_of_notMem (show t ∉ Iio (ε : ℝ) from htε)]
    exact bot_le

theorem finiteSpectralIntegral_pos
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n))
    (hpos : 0 < regularizedFiniteDimension d hd (finitePositiveClass n M)) :
    0 < finiteSpectralIntegral d n M := by
  rw [regularizedFiniteDimension_eval] at hpos
  obtain ⟨ε,hε⟩ := lt_iSup_iff.mp hpos
  obtain ⟨hεpos,hcut⟩ := lt_iSup_iff.mp hε
  exact (ENNReal.mul_pos hcut.ne' (by exact_mod_cast hεpos.ne')).trans_le
    (finiteSpectralIntegral_cut_lower_bound d hd n M ε)

variable [Nontrivial A]

theorem regularizedState_positive_nonzero (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (x : finiteCuntzSubmonoid (A := A)) (hx : x ≠ 0) :
    0 < regularizedFiniteDimension f.toAddHom f.monotone x := by
  apply pos_iff_ne_zero.mpr
  intro hz
  obtain ⟨k,hk⟩ := finiteCuntz_nonzero_orderUnit hsimple x hx finiteUnitClass
  have h := regularizedFiniteDimension_monotone f.toAddHom f.monotone hk
  rw [map_nsmul,hz,nsmul_zero] at h
  exact (not_le_of_gt (finiteState_regularized_unit hsimple y hy f).1) h

omit [Nontrivial A] in
theorem regularizedState_integral_finite (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) n M ≠ ⊤ := by
  apply finiteSpectralIntegral_ne_top _ (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
  exact ne_top_of_le_ne_top (finiteCuntz_state_finite hsimple y hy f _)
    (regularizedFiniteDimension_le f.toAddHom f.monotone _)

theorem regularizedState_integral_positive (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hM : M.1 ≠ 0) :
    0 < finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) n M := by
  apply finiteSpectralIntegral_pos _ (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
  erw [regularizedFiniteDimension_idempotent]
  exact regularizedState_positive_nonzero hsimple y hy f _
    (fun h => hM ((finitePositiveClass_eq_zero_iff n M).mp h))

omit [Nontrivial A] in
theorem regularizedState_integral_unit (y : finiteCuntzSubmonoid (A := A)) (f : StateSpace y) :
    finiteSpectralIntegral (regularizedFiniteDimension f.toAddHom f.monotone) 1 ⟨1,zero_le_one⟩ =
      f.1 finiteUnitClass := by
  rw [finiteSpectralIntegral_projection _ _ _ (by simp [IsIdempotentElem])]
  exact regularizedFiniteDimension_projection f.toAddHom f.monotone 1 ⟨1,zero_le_one⟩ (by simp [IsIdempotentElem])
end CuntzPureness

end

end OAI
