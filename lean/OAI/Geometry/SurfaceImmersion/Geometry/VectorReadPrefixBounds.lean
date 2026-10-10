import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Correction.GlobalShiftedSmoothing

namespace OAI

/-! Chart readings retain the unweighted derivative prefix of the true map. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma prefix_directional_bound {f : SmallModes.Base → V} (hf : ContDiff ℝ ∞ f)
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedEstimates.WeightedBound univ 1 j (C/s^(j-1)) f)
    (v : SmallModes.Base) (hv : ‖v‖ ≤ 1) :
    WeightedEstimates.WeightedBound univ s m C (SmallModes.coordDeriv v f) := by
  intro j hj x _
  have hh := ((hb (j+1) (by omega)).directional isOpen_univ zero_lt_one hf.contDiffOn v) j le_rfl x (mem_univ x)
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma shiftedBound_lower_prefix {q q' m m' : ℕ} {s C : ℝ} {F : M → V}
    (hb : A.ShiftedBound q m s C F) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : q' ≤ q) (hm : q'+m' ≤ q+m) : A.ShiftedBound q' m' s C F := by
  intro i j hj x
  apply le_trans _ (hb i j (hj.trans hm) x)
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one hs hs1 (Nat.sub_le_sub_left hq j)) (norm_nonneg _)

theorem vectorPlaneRead_prefix_bounds (i : A.centers) (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → ∀ j ≤ q+m,
      WeightedEstimates.WeightedBound univ 1 j (D*C/s^(j-q)) (A.vectorPlaneRead i F) := by
  classical
  choose D hD hd using fun j => A.vectorPlaneRead_bound (V := V) i j
  let T := ∑ j ∈ Finset.range (q+m+1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hD j)
  refine ⟨T,hT,?_⟩
  intro F s C hs hs1 hC hF hb j hj
  have hp : A.WeightedBound 1 j (C/s^(j-q)) F := fun k => (hb k).prefix hs hs1 hC hj
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (by positivity) hF hp
  apply hh.mono_const
  calc
    D j*(C/s^(j-q)) = D j*C/s^(j-q) := by ring
    _ ≤ T*C/s^(j-q) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC)
      (pow_nonneg hs.le _)

theorem vectorPlaneRead_directional_prefix_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound 1 m s C F → ∀ v : SmallModes.Base, ‖v‖ ≤ 1 →
      WeightedEstimates.WeightedBound univ s m (D*C) (SmallModes.coordDeriv v (A.vectorPlaneRead i F)) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_prefix_bounds (V := V) i 1 m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb v hv
  exact prefix_directional_bound (A.vectorPlaneRead_smooth i hF) hs (mul_nonneg hD hC)
    (fun j hj => hd F s C hs hs1 hC hF hb j (by omega)) v hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
