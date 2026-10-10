import OAI.Geometry.SurfaceImmersion.Atlas.AtlasPhaseCatalog
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadPrefixBounds

namespace OAI

/-! Every restored phase in the fixed catalog has a common derivative
budget, independent of the selected grid and the fast scale. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem linearPhaseCatalog_derivative_bounds (V : Finset SmallModes.Base) :
    ∃ P : ℕ → ℝ, (∀ m, 1 ≤ P m) ∧
      ∀ φ ∈ A.linearPhaseCatalog V, ∀ k : A.centers,
      ∀ (s : ℝ), 0 < s → s ≤ 1 → ∀ m v, ‖v‖ ≤ 1 →
        WeightedEstimates.WeightedBound univ s m (P m) (SmallModes.coordDeriv v (A.vectorPlaneRead k φ)) := by
  classical
  choose C hC hc using fun (φ : A.linearPhaseCatalog V) m =>
    A.exists_shifted_bound 1 m (A.linearPhaseCatalog_smooth V φ.val φ.property)
  choose D hD hd using fun (k : A.centers) m =>
    A.vectorPlaneRead_directional_prefix_bound (V := ℝ) k m
  let C₀ := fun m => ∑ φ : A.linearPhaseCatalog V, C φ m
  let D₀ := fun m => ∑ k : A.centers, D k m
  have hC₀ (m : ℕ) : 0 ≤ C₀ m := Finset.sum_nonneg (fun φ _ => hC φ m)
  have hD₀ (m : ℕ) : 0 ≤ D₀ m := Finset.sum_nonneg (fun k _ => hD k m)
  refine ⟨fun m => 1+D₀ m*C₀ m,fun m => le_add_of_nonneg_right
    (mul_nonneg (hD₀ m) (hC₀ m)),?_⟩
  intro φ hφ k s hs hs1 m v hv
  let f : A.linearPhaseCatalog V := ⟨φ,hφ⟩
  have hscale : A.ShiftedBound 1 m s (C f m) φ := by
    intro i j hj x
    have hh := hc f m i j hj x
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ 1*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) φ) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hs.le hs1) (norm_nonneg _)
      _ ≤ C f m := by simpa only [one_mul] using hh
  have hc' : C f m ≤ C₀ m :=
    Finset.single_le_sum (fun g _ => hC g m) (Finset.mem_univ f)
  have hd' : D k m ≤ D₀ m :=
    Finset.single_le_sum (fun i _ => hD i m) (Finset.mem_univ k)
  apply (hd k m φ s (C f m) hs hs1 (hC f m)
    (A.linearPhaseCatalog_smooth V φ hφ) hscale v hv).mono_const
  exact (mul_le_mul hd' hc' (hC f m) (hD₀ m)).trans
    (le_add_of_nonneg_left zero_le_one)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
