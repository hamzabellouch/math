import OAI.Analysis.SegmentLenses.Averaged

namespace OAI

/-!
# Primal projections and Euclidean coordinate bounds
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses


section PrimalProjections
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

def primalHead (H : Finset V) : Primal V →L[ℝ] Primal V :=
  ∑ v ∈ H, (coordinate v).smulRight (unitVector v)

def primalTail (H : Finset V) : Primal V →L[ℝ] Primal V :=
  ContinuousLinearMap.id ℝ (Primal V) - primalHead H

@[simp] theorem primalHead_apply (H : Finset V) (u : Primal V) :
    primalHead H u = ∑ v ∈ H, coordinate v u • unitVector v := by
  have _ := decidableEqV
  simp [primalHead]

theorem primalHead_test (H : Finset V) (u : Test V) :
    primalHead H (u : Primal V) = (Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) := by
  rw [primalHead_apply]
  conv_rhs => rw [test_as_sum]
  simp only [coordinate_apply_test, Test.coeff, Test.ofFinsupp]
  symm
  calc
    (∑ v ∈ (u.coeff.filter (· ∈ H)).support, (u.coeff.filter (· ∈ H)) v • unitVector v) =
        ∑ v ∈ H, (u.coeff.filter (· ∈ H)) v • unitVector v := by
      apply Finset.sum_subset
      · intro v hv
        exact (Finset.mem_filter.mp (by simpa only [Finsupp.support_filter] using hv)).2
      · intro v hv hnv
        rw [Finsupp.notMem_support_iff.mp hnv, zero_smul]
    _ = ∑ v ∈ H, u.coeff v • unitVector v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finsupp.filter_apply, ite_eq_left hv]

theorem primalTail_test (H : Finset V) (u : Test V) :
    primalTail H (u : Primal V) = (Test.ofFinsupp (u.coeff.filter (· ∉ H)) : Test V) := by
  change (u : Primal V) - primalHead H (u : Primal V) = _
  rw [primalHead_test]
  have he : u - Test.ofFinsupp (u.coeff.filter (· ∈ H)) =
      Test.ofFinsupp (u.coeff.filter (· ∉ H)) := by
    change u.coeff - u.coeff.filter (· ∈ H) = u.coeff.filter (· ∉ H)
    ext v
    by_cases hv : v ∈ H <;> simp [hv]
  exact (map_sub (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V) _ _).symm.trans
    (congrArg (fun u : Test V => (u : Primal V)) he)


theorem head_adjoint (H : Finset V) (x : FullDual V) (u : Primal V) :
    head H x u = x (primalHead H u) := by
  simp only [head, primalHead_apply, _root_.sum_apply,
    _root_.smul_apply, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem tail_adjoint (H : Finset V) (x : FullDual V) (u : Primal V) :
    tail H x u = x (primalTail H u) := by
  change x u - head H x u = x (u - primalHead H u)
  rw [map_sub, head_adjoint]

@[simp] theorem coordinate_primalHead (H : Finset V) (v : V) (u : Primal V) :
    coordinate v (primalHead H u) = if v ∈ H then coordinate v u else 0 := by
  simp [primalHead_apply, coordinate_unitVector]

theorem primalHead_fix (H : Finset V) (u : Test V) (hu : u.coeff.support ⊆ H) :
    primalHead H (u : Primal V) = u := by
  rw [primalHead_test]
  congr 1
  change u.coeff.filter (· ∈ H) = u.coeff
  ext v
  by_cases hv : v ∈ H
  · simp [hv]
  · have hz : u.coeff v = 0 := Finsupp.notMem_support_iff.mp (fun h => hv (hu h))
    simp [hv, hz]

variable [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V] [IntervalSegments V]

theorem norm_primalHead_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (u : Primal V) :
    ‖primalHead H u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (p := fun u => ‖primalHead H u‖ ≤ ‖u‖)
    (isClosed_le (primalHead H).continuous.norm continuous_norm) ?_
  intro u
  rw [primalHead_test, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact norm_headTest_le hH u.coeff

theorem norm_primalTail_le {H : Finset V} (hH : Ancestral (· ≤ ·) H) (u : Primal V) :
    ‖primalTail H u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (p := fun u => ‖primalTail H u‖ ≤ ‖u‖)
    (isClosed_le (primalTail H).continuous.norm continuous_norm) ?_
  intro u
  rw [primalTail_test, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact norm_tailTest_le hH u.coeff

end PrimalProjections


section CoordinateEuclidean
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]


theorem singleton_square_sum_le (s : Finset V) (u : Test V) :
    ∑ v ∈ s, u.coeff v ^ 2 ≤ ‖u‖ ^ 2 := by
  have _ := decidableEqV
  have h := indexed_test_bound u.coeff (fun v : s => ({v.val} : Finset V))
    (fun v => Or.inr (SegmentSystem.singleton v.val))
    (fun v w hvw => Finset.disjoint_singleton.mpr (fun h => hvw (Subtype.ext h)))
  simp only [Finset.sum_singleton] at h
  rw [Finset.sum_coe_sort s (fun v => u.coeff v ^ 2)] at h
  exact h

theorem norm_coordinate_sum_le (s : Finset V) (a : V → ℝ) :
    ‖∑ v ∈ s, a v • coordinate v‖ ≤ Real.sqrt (∑ v ∈ s, a v ^ 2) := by
  apply dual_norm_le _ (Real.sqrt_nonneg _)
  intro u
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun v => |a v|) (fun v => |u.coeff v|)
  have hsing := singleton_square_sum_le s u
  have hs : Real.sqrt (∑ v ∈ s, u.coeff v ^ 2) ≤ ‖u‖ :=
    (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hsing⟩
  calc
    |(∑ v ∈ s, a v • coordinate v) (u : Primal V)| =
        |∑ v ∈ s, a v * u.coeff v| := by
      simp only [_root_.sum_apply, _root_.smul_apply, coordinate_apply_test, smul_eq_mul]
    _ ≤ ∑ v ∈ s, |a v| * |u.coeff v| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun v => a v * u.coeff v) s
    _ ≤ Real.sqrt (∑ v ∈ s, a v ^ 2) * Real.sqrt (∑ v ∈ s, u.coeff v ^ 2) := by
      simpa only [sq_abs] using hcs
    _ ≤ Real.sqrt (∑ v ∈ s, a v ^ 2) * ‖u‖ :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)

theorem norm_predualCoordinate_sum_le (s : Finset V) (a : V → ℝ) :
    ‖∑ v ∈ s, a v • predualCoordinate v‖ ≤ Real.sqrt (∑ v ∈ s, a v ^ 2) := by
  have he : ((∑ v ∈ s, a v • predualCoordinate v : CoordinatePredual V) : FullDual V) =
      ∑ v ∈ s, a v • coordinate v := by simp [predualCoordinate]
  change ‖((∑ v ∈ s, a v • predualCoordinate v : CoordinatePredual V) : FullDual V)‖ ≤ _
  rw [he]
  exact norm_coordinate_sum_le s a



local instance predualACM : AddCommMonoid (CoordinatePredual V) :=
  (inferInstance : NormedAddCommGroup (CoordinatePredual V)).toAddCommMonoid
local instance predualTop : TopologicalSpace (CoordinatePredual V) :=
  (inferInstance : NormedAddCommGroup (CoordinatePredual V)).toUniformSpace.toTopologicalSpace
local instance predualModule : Module ℝ (CoordinatePredual V) :=
  (inferInstance : NormedSpace ℝ (CoordinatePredual V)).toModule


theorem functional_coordinate_square_sum (L : StrongDual ℝ (CoordinatePredual V)) (s : Finset V) :
    ∑ v ∈ s, L (predualCoordinate v) ^ 2 ≤ ‖L‖ ^ 2 := by
  let q := ∑ v ∈ s, L (predualCoordinate v) • predualCoordinate v
  let S := ∑ v ∈ s, L (predualCoordinate v) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : L q = S := by simp only [q, S, map_sum, map_smul, smul_eq_mul, pow_two]
  have hq : ‖q‖ ≤ Real.sqrt S := norm_predualCoordinate_sum_le s _
  have h := L.le_opNorm q
  rw [hp, Real.norm_eq_abs, abs_of_nonneg hS] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left hq (norm_nonneg _))
  have hs := Real.sq_sqrt hS
  nlinarith [Real.sqrt_nonneg S, norm_nonneg L]


theorem functional_coordinates_summable_sq (L : StrongDual ℝ (CoordinatePredual V)) :
    Summable (fun v => L (predualCoordinate v) ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (functional_coordinate_square_sum L)



theorem distinct_coordinates_weakly_null (v : ℕ → V) (hv : Function.Injective v)
    (L : StrongDual ℝ (CoordinatePredual V)) :
    Filter.Tendsto (fun n => L (predualCoordinate (v n))) Filter.atTop (nhds 0) := by
  have hs : Summable (fun n => L (predualCoordinate (v n)) ^ 2) :=
    (functional_coordinates_summable_sq L).comp_injective hv
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  have hn : Filter.Tendsto (fun n => ‖L (predualCoordinate (v n))‖) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

end CoordinateEuclidean


end SegmentLenses

end

end OAI
