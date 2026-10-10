import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveFrameBounds
import OAI.Geometry.SurfaceImmersion.Primitive.FinitePrimitiveOperatorTolerance
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveOperatorMask

namespace OAI

/-! Independent cutoff and phase perturbations give uniform control of
the actual operator in every chart of the fixed primitive atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance actualToleranceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance actualToleranceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance actualToleranceDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualToleranceDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualToleranceSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualToleranceSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem primitive_operator_tolerance
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (phi₀ : (B.centers × Fin 3) → M → ℝ)
    (hphi₀ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi₀ a))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ psi phi : (B.centers × Fin 3) → M → ℝ,
      (∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1)) →
      (∀ a p, |psi a p-B.weight a.1 p| < eps) →
      (∀ (i : B.centers) (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
        ‖B.covectorFrame i p (B.primitivePhaseCovector phi a p)-
          B.covectorFrame i p (B.primitivePhaseCovector phi₀ a p)‖ < eps) →
      ∀ i p, p ∈ tsupport (B.weight i) →
        ‖B.tensorOperatorFrame i p (B.primitiveFullOperator P psi phi p)-
          B.tensorOperatorFrame i p
            (B.primitiveFullOperator P (fun a => B.weight a.1) phi₀ p)‖ < eta := by
  classical
  obtain ⟨Dq,hDq,hq⟩ := B.coefficientFrame_bound P hQ
  choose Dv hDv hv using fun a => B.covectorFrame_bound (phi₀ a) (hphi₀ a)
  let D : ℝ := Dq+1+∑ a, Dv a
  have hDqD : Dq ≤ D := by
    have := Finset.sum_nonneg (s := Finset.univ) (fun a _ => zero_le_one.trans (hDv a)); dsimp only [D]; linarith
  have hD1 : 1 ≤ D := by linarith
  have hDvD (a : B.centers × Fin 3) : Dv a ≤ D := by
    have := Finset.single_le_sum (fun a _ => zero_le_one.trans (hDv a)) (Finset.mem_univ a)
    dsimp only [D]; linarith
  obtain ⟨eps,heps,_,hnear⟩ := finite_primitive_operator_tolerance (ι := B.centers × Fin 3) D heta
  refine ⟨eps,heps,?_⟩
  intro psi phi hs hw hd i p hp
  let S : Set (B.centers × Fin 3) := {a | p ∈ tsupport (B.weight a.1)}
  let q := fun a => if a ∈ S then B.coefficientFrame P i a p else 0
  let v₀ := fun a => B.covectorFrame i p (B.primitivePhaseCovector phi₀ a p)
  let v := fun a => if a ∈ S then B.covectorFrame i p (B.primitivePhaseCovector phi a p) else v₀ a
  let z₀ : PrimitiveOperatorData (B.centers × Fin 3) := ((q,fun a => B.weight a.1 p),v₀)
  let z : PrimitiveOperatorData (B.centers × Fin 3) := ((q,fun a => psi a p),v)
  have hqD : ‖q‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD1)).mpr
    intro a
    dsimp [q]
    split_ifs with ha
    · exact (hq i a p hp ha).trans hDqD
    · simpa only [norm_zero] using zero_le_one.trans hD1
  have hwD : ‖fun a : B.centers × Fin 3 => B.weight a.1 p‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD1)).mpr
    intro a
    have hh := Finset.single_le_sum (fun b _ => sq_nonneg (B.weight b p)) (Finset.mem_univ a.1)
    rw [B.partition p] at hh
    have hh' : |B.weight a.1 p| ≤ 1 := by nlinarith [sq_abs (B.weight a.1 p),abs_nonneg (B.weight a.1 p)]
    exact (show ‖B.weight a.1 p‖ ≤ 1 by simpa only [Real.norm_eq_abs] using hh').trans hD1
  have hvD : ‖v₀‖ ≤ D := by
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hD1)).mpr
    intro a
    exact (hv a i p hp).trans (hDvD a)
  have hz₀ : ‖z₀‖ ≤ D := by
    exact max_le (max_le hqD hwD) hvD
  have hdist : ‖z-z₀‖ < eps := by
    change max (max ‖q-q‖ ‖(fun a => psi a p)-(fun a => B.weight a.1 p)‖) ‖v-v₀‖ < eps
    rw [sub_self,norm_zero]
    apply max_lt
    · apply max_lt heps
      apply (pi_norm_lt_iff heps).mpr
      intro a
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using hw a p
    · apply (pi_norm_lt_iff heps).mpr
      intro a
      dsimp [v]
      split_ifs with ha
      · exact hd i a p hp ha
      · simpa only [sub_self,norm_zero] using heps
  have hz := hnear z₀ z hz₀ hdist
  have hzero (a : B.centers × Fin 3) (ha : a ∉ S) : psi a p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => ha (hs a hh))
  have hzero₀ (a : B.centers × Fin 3) (ha : a ∉ S) : B.weight a.1 p = 0 :=
    image_eq_zero_of_notMem_tsupport ha
  rw [B.primitiveFullOperator_frame P psi phi i (B.weight_support i hp),
    B.primitiveFullOperator_frame P (fun a => B.weight a.1) phi₀ i (B.weight_support i hp)]
  rw [completedPrimitiveOperator_mask _ _ _ v₀ S hzero,
    completedPrimitiveOperator_mask _ _ _ v₀ S hzero₀]
  simpa only [primitiveDataOperator,z,z₀,v₀,v,q,ite_self] using hz

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
