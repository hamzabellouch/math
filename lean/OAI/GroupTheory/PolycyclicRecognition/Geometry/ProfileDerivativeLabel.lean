import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearSupportSymmetries
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteInvariantOrbit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries

namespace OAI

/-! # Infinitesimal profile constraints give a finite height-symmetry label -/

noncomputable section

namespace PolycyclicRecognition

open Module Set

/-- A horizontal linear derivative factors through height and is a support
isometry once the convex-increment and segment-volume inequalities hold.
This first step lands in the full isometry group of the segment norm. -/
theorem derivative_eq_support_symmetry
    {V W I B J : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → linearSupportSymmetryGroup D)
    (hconv : ∀ v, M v ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hlower : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (M v)) :
    ∃ T : linearSupportSymmetryGroup D, M = T.val.toLinearMap.comp π := by
  let : Norm W := ⟨D.segmentSupport⟩
  let core : NormedSpace.Core ℝ W := D.normCore
  let : NormedAddCommGroup W := NormedAddCommGroup.ofCore core
  let : NormedSpace ℝ W := NormedSpace.ofCore core
  have hupper (v : V) : ‖M v‖ ≤ ‖π v‖ := by
    have hball : range (fun j => (A j).val (π v)) ⊆ Metric.closedBall 0 ‖π v‖ := by
      rintro _ ⟨j, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact ((A j).property (π v)).le
    have hh := (convexHull_min hball (convex_closedBall (0 : W) ‖π v‖)) (hconv v)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh
  have hzero (v : V) (hv : π v = 0) : M v = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hv, norm_zero] using hupper v
  obtain ⟨σ, hσ⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hπσ (w : W) : π (σ w) = w := LinearMap.congr_fun hσ w
  let T := M.comp σ
  have hfactor (v : V) : T (π v) = M v := by
    have hh := hzero (v - σ (π v)) (by rw [map_sub, hπσ, sub_self])
    rw [map_sub] at hh
    exact (sub_eq_zero.mp hh).symm
  have hnorm (w : W) : ‖T w‖ = ‖w‖ := by
    apply le_antisymm
    · simpa only [T, LinearMap.comp_apply, hπσ] using hupper (σ w)
    · change D.segmentSupport w ≤ D.segmentSupport (M (σ w))
      simpa only [hπσ] using hlower (σ w)
  have hinj : Function.Injective T := by
    intro w u h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← hnorm (w - u), map_sub, h, sub_self, norm_zero]
  have hsurj : Function.Surjective T := LinearMap.surjective_of_injective hinj
  let e := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  refine ⟨⟨e, hnorm⟩, ?_⟩
  ext v
  exact (hfactor v).symm

/-- The convex orbit constraint selects a member of the original family,
even when that family is smaller than the full segment-norm isometry group. -/
theorem derivative_eq_one_of_labels
    {V W I B J : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → linearSupportSymmetryGroup D)
    (hconv : ∀ v, M v ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hlower : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (M v)) :
    ∃ j, M = (A j).val.toLinearMap.comp π := by
  obtain ⟨T, hT⟩ := derivative_eq_support_symmetry D π M hπ A hconv hlower
  let Γ := linearSupportSymmetryGroup D
  let : Fintype Γ := Fintype.ofFinite Γ
  let e : W ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) :=
    (Module.finBasis ℝ W).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm
  have hconvW (w : W) : T.val w ∈ convexHull ℝ (range fun j => (A j).val w) := by
    obtain ⟨v, hv⟩ := hπ w
    have hh := hconv v
    rw [hT] at hh
    change T.val (π v) ∈ convexHull ℝ (range fun j => (A j).val (π v)) at hh
    rwa [hv] at hh
  obtain ⟨j, hj⟩ := exists_eq_label_of_finite_group_convex_orbit Γ e.toLinearMap
    e.injective T A hconvW
  exact ⟨j, hj ▸ hT⟩

/-- In particular, a family of template-preserving labels stays in that
same family under the infinitesimal profile argument. -/
theorem derivative_eq_one_of_template_labels
    {V W I B J : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J]
    (D : SupportDatum W I B) (π M : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup D)
    (hconv : ∀ v, M v ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hlower : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (M v)) :
    ∃ j, M = (A j).val.toLinearMap.comp π := by
  exact derivative_eq_one_of_labels D π M hπ
    (fun j => ⟨(A j).val, templateSymmetry_mem_linearSupportSymmetry D (A j)⟩) hconv hlower

end PolycyclicRecognition

end

end OAI
