import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.DirectionH1

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume GeometricHilbert
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

local instance : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance : FiniteDimensional ℝ (MetricForms.Form Space 2) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

lemma formCoordinates_lower : ∃ C : ℝ, 0 < C ∧ ∀ v : MetricForms.Form Space 2,
    ‖v‖^2 ≤ C * ‖formCoordinates 2 v‖^2 := by
  obtain ⟨K,hK,hb⟩ := (formCoordinates 2).toLinearMap.injective_iff_antilipschitz.mp
    (FiberCoordinates.complexCoordinates_injective (stdOrthonormalBasis ℝ Space).toBasis 2)
  refine ⟨(K:ℝ)^2,by exact sq_pos_of_pos (by exact_mod_cast hK),?_⟩
  intro v
  have h : ‖v‖ ≤ (K:ℝ)*‖formCoordinates 2 v‖ := by
    simpa only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] using hb.le_mul_dist v 0
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) h 2

include hs hD in
lemma localized_metric_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : smoothForms X 2,
      (∫ x, (A.partition p x)^2 * GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) ≤
        C * ‖localizeL2 A 2 a p‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coordinate_metric_two_bounds A J α hs ht D hD p
  obtain ⟨K,hK,hform⟩ := formCoordinates_lower
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro a
  rw [localizeL2_apply,schwartz_l2_norm_sq,← integral_localizedPairing A J α ht hs p (Or.inr rfl) a.property]
  have hint : Integrable (fun x => ‖localizedLinear A 2 p a x‖^2) := by
    exact (memLp_two_iff_integrable_sq_norm (localizedLinear A 2 p a).continuous.aestronglyMeasurable).mp
      ((localizedLinear A 2 p a).memLp 2 volume)
  have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x =>
      mul_nonneg (show 0 ≤ chartDensity J α p.val x from Real.sqrt_nonneg _)
        (MetricForms.pairing_self_nonneg (coordinateMetric J α ht p.val x) (localizedFunction A p a.val x))))
    (hint.const_mul (C*K)) (Filter.Eventually.of_forall (fun x => ?_))
  · simpa only [integral_const_mul] using h
  · by_cases hx : x ∈ coordinateSupport A p
    · exact ((hbound x hx (localizedFunction A p a.val x)).2).trans
        ((mul_le_mul_of_nonneg_left (hform (localizedFunction A p a.val x)) hC.le).trans_eq (mul_assoc _ _ _).symm)
    · change _ ≤ C*K*‖formCoordinates 2 (localizedFunction A p a.val x)‖^2
      have hz : localizedFunction A p a.val x = 0 := localizedFunction_zero_off A p a.val hx
      have hp : MetricForms.pairing (coordinateMetric J α ht p.val x)
          (localizedFunction A p a.val x) (localizedFunction A p a.val x) = 0 :=
        (MetricForms.pairing_self_eq_zero _ _).mpr hz
      dsimp only
      rw [hp,hz,map_zero,norm_zero]
      simp

include hs hD in

theorem metric_norm_le_chart : ∃ C : ℝ, 0 < C ∧ ∀ a : PreL2 A J α hs ht true,
    ‖a‖^2 ≤ C * ‖localizeL2 A 2 a‖^2 := by
  classical
  have hi := geometricVolume_finite A J α hs ht
  let := hi
  choose C hC hbound using localized_metric_bound A J α hs ht D hD
  let B := 1 + ∑ p : A.centers, C p
  have hB : 0 < B := by
    have hsum : 0 ≤ ∑ p : A.centers, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hCB (p : A.centers) : C p ≤ B := by
    exact (Finset.single_le_sum (fun q _ => (hC q).le) (Finset.mem_univ p)).trans (by change (∑ p : A.centers, C p) ≤ 1 + (∑ p : A.centers, C p); linarith)
  let N : ℝ := Fintype.card A.centers
  refine ⟨(N+1)*B,mul_pos (by dsimp [N]; positivity) hB,?_⟩
  intro a
  let f : X → ℝ := GeometricAdjoint.pairing J α ht a.val a.val
  have hf : Integrable f (geometricVolume A J α) :=
    (GeometricAdjoint.pairing_two_smooth J α hs ht a.property a.property).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hρ (p : A.centers) : Integrable (fun x => (A.partition p x)^2 * f x) (geometricVolume A J α) :=
    (((A.partition p).contMDiff.continuous.pow 2).mul
      (GeometricAdjoint.pairing_two_smooth J α hs ht a.property a.property).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum (x : X) : f x ≤ N * (∑ p : A.centers, (A.partition p x)^2*f x) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun p : A.centers => A.partition p x)
    rw [partition_sum A x,one_pow] at h
    have hm := mul_le_mul_of_nonneg_right h (MetricForms.pairing_self_nonneg (GeometricAdjoint.pointMetric J α ht x) (a.val x))
    simpa only [N,f,GeometricAdjoint.pairing,one_mul,Finset.card_univ,Finset.sum_mul,mul_assoc] using hm
  have hI := integral_mono hf
    ((integrable_finsetSum Finset.univ (fun p _ => hρ p)).const_mul N) hsum
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun p _ => hρ p)] at hI
  have hc : (∑ p : A.centers, ∫ x, (A.partition p x)^2*f x ∂geometricVolume A J α) ≤
      B * ‖localizeL2 A 2 a‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    exact (hbound p a).trans (mul_le_mul_of_nonneg_right (hCB p) (sq_nonneg _))
  rw [preL2_norm_sq]
  change (∫ x, f x ∂geometricVolume A J α) ≤ _
  have hm := mul_le_mul_of_nonneg_left hc (by dsimp [N]; positivity : 0 ≤ N)
  have hn := mul_nonneg hB.le (sq_nonneg ‖localizeL2 A 2 a‖)
  nlinarith
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
