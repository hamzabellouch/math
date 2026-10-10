import OAI.Geometry.SurfaceImmersion.Geometry.EuclideanRestoration
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

namespace OAI

/-! A fixed atlas controls a single Euclidean restored correction, with a
constant independent of its center, support radius and jet tensor. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem single_euclidean_restore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (i : A.centers) (f : Plane → Space) (C : ℝ),
      0 ≤ C → ContDiff ℝ ∞ f → WeightedEstimates.WeightedBound univ 1 m C f →
      A.WeightedBound 1 m (D*C) (euclideanRestore (i : M) (A.outer i) f) := by
  classical
  let e := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap
  let K : ℝ := max 1 ‖e‖ ^ m
  have hK : 0 ≤ K := pow_nonneg (le_max_of_le_left zero_le_one) _
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := Space) m
  refine ⟨D*K,mul_nonneg hD hK,?_⟩
  intro i f C hC hf hb
  have he : WeightedEstimates.WeightedBound univ 1 m (K*C) (f ∘ e) := by
    intro j hj x hx
    rw [iteratedFDerivWithin_univ,e.iteratedFDeriv_comp_right hf x (by simp)]
    simp only [one_pow,one_mul]
    have hnorm := (iteratedFDeriv ℝ j f (e x)).norm_compContinuousLinearMap_le
      (fun _ => e)
    have hp : ‖e‖^j ≤ K := by
      exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖e‖) _).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖e‖) hj)
    have hv := hb j hj (e x) (mem_univ _)
    simp only [iteratedFDerivWithin_univ,one_pow,one_mul] at hv
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f (e x)‖ * ∏ _ : Fin j, ‖e‖ := hnorm
      _ = ‖iteratedFDeriv ℝ j f (e x)‖ * ‖e‖^j := by simp
      _ ≤ C*K := mul_le_mul hv hp (pow_nonneg (norm_nonneg _) _) hC
      _ = K*C := mul_comm _ _
  have hr := hd (fun k => if k = i then f ∘ e else 0) 1 (K*C)
    zero_lt_one le_rfl (mul_nonneg hK hC)
    (fun k => by split_ifs; exact hf.comp e.contDiff; exact contDiff_const)
    (fun k => by split_ifs; exact he; exact (weightedBound_zero univ 1 m).mono_const (mul_nonneg hK hC))
  have heq : (∑ k : A.centers, restore (k : M) (A.outer k)
      (if k = i then f ∘ e else 0)) = euclideanRestore (i : M) (A.outer i) f := by
    funext p
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [euclideanRestore,e]
    · intro j _ hji
      simp [hji,restore]
    · simp
  rw [heq] at hr
  simpa only [mul_assoc] using hr

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
