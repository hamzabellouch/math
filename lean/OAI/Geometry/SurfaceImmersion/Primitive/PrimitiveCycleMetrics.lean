import OAI.Geometry.SurfaceImmersion.Primitive.PositiveAtlasPrimitives

namespace OAI

/-! A finite positive primitive family can be repeated in equally weighted
cycles. Every partial cycle is an actual smooth positive metric, and every
completed cycle advances by exactly the prescribed fraction of the tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

local instance cycleFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance cycleDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance cycleDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance cycleSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M) (P : A.centers → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)
local instance : DecidableEq (A.centers × Fin 3) := Classical.decEq _

def cyclePrimitiveAmplitude (N : ℕ) (a : A.centers × Fin 3) : M → ℝ :=
  fun p => A.positivePrimitiveAmplitude P u a p / Real.sqrt (N : ℝ)

lemma cyclePrimitiveAmplitude_square (N : ℕ)
    (a : A.centers × Fin 3) (p : M) :
    (A.cyclePrimitiveAmplitude P u N a p)^2 =
      (N : ℝ)⁻¹ * (A.positivePrimitiveAmplitude P u a p)^2 := by
  unfold cyclePrimitiveAmplitude
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  exact div_eq_inv_mul _ _

lemma cyclePrimitiveAmplitude_pos_iff {N : ℕ} (hN : 0 < N)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (a : A.centers × Fin 3) (p : M) :
    0 < A.cyclePrimitiveAmplitude P u N a p ↔ A.weight a.1 p ≠ 0 := by
  change 0 < A.positivePrimitiveAmplitude P u a p / Real.sqrt (N : ℝ) ↔ _
  rw [div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast hN))]
  exact A.positivePrimitiveAmplitude_pos_iff P u hpos a p

def primitiveCycleTensor (N c : ℕ) (s : Finset (A.centers × Fin 3))
    (p : M) : CovariantTwoTensor p :=
  ((c : ℝ) / (N : ℝ)) • u p +
    (N : ℝ)⁻¹ • ∑ a ∈ s, A.positivePrimitiveTensor P u a p

lemma primitiveCycleTensor_empty (N c : ℕ) (p : M) :
    A.primitiveCycleTensor P u N c ∅ p = ((c : ℝ) / (N : ℝ)) • u p := by
  simp only [primitiveCycleTensor, Finset.sum_empty, smul_zero, add_zero]

lemma primitiveCycleTensor_start (N : ℕ) (p : M) :
    A.primitiveCycleTensor P u N 0 ∅ p = 0 := by
  rw [A.primitiveCycleTensor_empty]
  simp only [Nat.cast_zero, zero_div, zero_smul]

lemma primitiveCycleTensor_insert (N c : ℕ) (s : Finset (A.centers × Fin 3))
    (a : A.centers × Fin 3) (ha : a ∉ s) (p : M) :
    A.primitiveCycleTensor P u N c (insert a s) p =
      A.primitiveCycleTensor P u N c s p + (N : ℝ)⁻¹ • A.positivePrimitiveTensor P u a p := by
  classical
  simp only [primitiveCycleTensor, Finset.sum_insert ha, smul_add]
  abel

lemma primitiveCycleTensor_insert_apply (N c : ℕ)
    (s : Finset (A.centers × Fin 3)) (a : A.centers × Fin 3) (ha : a ∉ s)
    (p : M) (v w : TangentSpace planeModel p) :
    A.primitiveCycleTensor P u N c (insert a s) p v w =
      A.primitiveCycleTensor P u N c s p v w +
        (A.cyclePrimitiveAmplitude P u N a p)^2 *
          (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p v) *
          (show ℝ from mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p w) := by
  rw [A.primitiveCycleTensor_insert P u N c s a ha p]
  change _ + (N : ℝ)⁻¹ * A.positivePrimitiveTensor P u a p v w = _
  rw [A.positivePrimitiveTensor_apply, A.cyclePrimitiveAmplitude_square P u N]
  let dv : ℝ := mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p v
  let dw : ℝ := mfderiv planeModel 𝓘(ℝ) (atlasPhase (a.1 : M) ((P a.1).ξ a.2)) p w
  let r : ℝ := A.primitiveCycleTensor P u N c s p v w
  change r + (N : ℝ)⁻¹ * ((A.positivePrimitiveAmplitude P u a p)^2 * dv * dw) =
    r + ((N : ℝ)⁻¹ * (A.positivePrimitiveAmplitude P u a p)^2) * dv * dw
  ring

lemma primitiveCycleTensor_complete
    (hu : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (N c : ℕ) (p : M) :
    A.primitiveCycleTensor P u N c Finset.univ p =
      A.primitiveCycleTensor P u N (c + 1) ∅ p := by
  rw [primitiveCycleTensor, A.sum_positivePrimitiveTensor P u hu hpos,
    A.primitiveCycleTensor_empty, ← add_smul]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, add_mul, one_mul]

lemma primitiveCycleTensor_finish {N : ℕ} (hN : 0 < N) (p : M) :
    A.primitiveCycleTensor P u N N ∅ p = u p := by
  rw [A.primitiveCycleTensor_empty, div_self (by exact_mod_cast (Nat.ne_of_gt hN)), one_smul]

lemma positivePrimitiveSum_nonneg
    (hu : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (p : M) (v : TangentSpace planeModel p) : 0 ≤ u p v v := by
  rw [← A.sum_positivePrimitiveTensor P u hu hpos p]
  simp only [sum_apply]
  exact Finset.sum_nonneg (fun a _ => A.positivePrimitiveTensor_nonneg P u a p v)

lemma primitiveCycleTensor_nonneg
    (hu : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 ≤ (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (N c : ℕ) (s : Finset (A.centers × Fin 3)) (p : M)
    (v : TangentSpace planeModel p) : 0 ≤ A.primitiveCycleTensor P u N c s p v v := by
  change 0 ≤ (c : ℝ) / (N : ℝ) * u p v v +
    (N : ℝ)⁻¹ * (∑ a ∈ s, A.positivePrimitiveTensor P u a p) v v
  apply add_nonneg
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg c) (Nat.cast_nonneg N))
      (A.positivePrimitiveSum_nonneg P u hu hpos p v)
  · apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    simp only [sum_apply]
    exact Finset.sum_nonneg (fun a _ => A.positivePrimitiveTensor_nonneg P u a p v)

lemma primitiveCycleTensor_symmetric
    (hu : ∀ p v w, u p v w = u p w v)
    (N c : ℕ) (s : Finset (A.centers × Fin 3)) (p : M)
    (v w : TangentSpace planeModel p) :
    A.primitiveCycleTensor P u N c s p v w = A.primitiveCycleTensor P u N c s p w v := by
  change (c : ℝ) / (N : ℝ) * u p v w +
    (N : ℝ)⁻¹ * (∑ a ∈ s, A.positivePrimitiveTensor P u a p) v w =
    (c : ℝ) / (N : ℝ) * u p w v +
      (N : ℝ)⁻¹ * (∑ a ∈ s, A.positivePrimitiveTensor P u a p) w v
  simp only [sum_apply]
  rw [hu p v w]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  exact A.positivePrimitiveTensor_symmetric P u a p v w

variable [CompactSpace M]

lemma primitiveCycleTensor_smooth
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (N c : ℕ) (s : Finset (A.centers × Fin 3)) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.primitiveCycleTensor P u N c s p)) := by
  apply hu.const_smul_section.add_section
  apply ContMDiff.const_smul_section
  apply ContMDiff.sum_section
  intro a _
  exact A.positivePrimitiveTensor_smooth P u hu hpos a

def primitiveCycleMetric (g : SmoothMetric M)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsymm : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ i j p, p ∈ tsupport (A.weight i) →
      0 < (P i).Q j (A.tensorChartRead i u (chart (i : M) p)))
    (N c : ℕ) (s : Finset (A.centers × Fin 3)) : SmoothMetric M where
  inner p := g.inner p + A.primitiveCycleTensor P u N c s p
  symm p v w := by
    change g.inner p v w + A.primitiveCycleTensor P u N c s p v w = _
    rw [g.symm p v w, A.primitiveCycleTensor_symmetric P u hsymm N c s p v w]
    rfl
  pos p v hv := lt_of_lt_of_le (g.pos p v hv)
    (le_add_of_nonneg_right (A.primitiveCycleTensor_nonneg P u hsymm
      (fun i j p hp => (hpos i j p hp).le) N c s p v))
  isVonNBounded p := (g.isVonNBounded p).subset (by
    intro v hv
    exact lt_of_le_of_lt (le_add_of_nonneg_right (A.primitiveCycleTensor_nonneg P u hsymm
      (fun i j p hp => (hpos i j p hp).le) N c s p v)) hv)
  contMDiff := g.contMDiff.add_section (A.primitiveCycleTensor_smooth P u hu hpos N c s)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
