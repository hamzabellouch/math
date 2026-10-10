import OAI.Analysis.KadisonKastler.CountableAmplificationNormal
import OAI.Analysis.KadisonKastler.SpatialAssociator

namespace OAI

/-! # Countable sums commute with the spatial Hilbert tensor product

The coordinate tensor map preserves inner products on algebraic tensors.
Its completion is onto because it contains every finitely supported tensor
vector. This is the concrete amplification bridge for the constructed
faithful cyclic representation.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def countableTensorVector (x : CountableHilbertSum H) (y : K) :
    CountableHilbertSum (SpatialHilbert H K) :=
  ⟨fun n => ((x n ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K), by
    apply ((lp.memℓp x).norm.const_mul ‖y‖).mono
    intro n
    simp only [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, mul_comm, le_refl]⟩

@[simp] theorem countableTensorVector_apply (x : CountableHilbertSum H) (y : K) (n : ℕ) :
    countableTensorVector x y n =
      ((x n ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) := rfl

def countableTensorBilinear :
    CountableHilbertSum H →ₗ[ℂ] K →ₗ[ℂ] CountableHilbertSum (SpatialHilbert H K) where
  toFun x :=
    { toFun := countableTensorVector x
      map_add' := by intros; ext n; simp [TensorProduct.tmul_add, UniformSpace.Completion.coe_add]
      map_smul' := by intros; ext n; simp [UniformSpace.Completion.coe_smul] }
  map_add' := by intros; ext y n; simp [TensorProduct.add_tmul, UniformSpace.Completion.coe_add]
  map_smul' := by
    intro c x
    ext y n
    change (((c • x n) ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) =
      c • ((x n ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K)
    rw [← TensorProduct.smul_tmul', UniformSpace.Completion.coe_smul]

theorem inner_countableTensorVector (x x' : CountableHilbertSum H) (y y' : K) :
    inner ℂ (countableTensorVector x y) (countableTensorVector x' y') =
      inner ℂ x x' * inner ℂ y y' := by
  simp only [lp.inner_eq_tsum, countableTensorVector_apply,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]
  exact tsum_mul_right

def countableTensorAlgebraic :
    CountableHilbertSum H ⊗[ℂ] K →ₗ[ℂ] CountableHilbertSum (SpatialHilbert H K) :=
  TensorProduct.lift countableTensorBilinear

@[simp] theorem countableTensorAlgebraic_tmul (x : CountableHilbertSum H) (y : K) :
    countableTensorAlgebraic (x ⊗ₜ[ℂ] y) = countableTensorVector x y := rfl

theorem inner_countableTensorAlgebraic (z w : CountableHilbertSum H ⊗[ℂ] K) :
    inner ℂ (countableTensorAlgebraic z) (countableTensorAlgebraic w) = inner ℂ z w := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, inner_add_left, ha, hb]
  | tmul x y =>
    induction w using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, inner_add_right, ha, hb]
    | tmul x' y' =>
      simp only [countableTensorAlgebraic_tmul, inner_countableTensorVector,
        TensorProduct.inner_tmul]

def countableTensorIsometry :
    SpatialHilbert (CountableHilbertSum H) K →ₗᵢ[ℂ]
      CountableHilbertSum (SpatialHilbert H K) :=
  (countableTensorAlgebraic.isometryOfInner inner_countableTensorAlgebraic).fromCompletion

@[simp] theorem countableTensorIsometry_tmul (x : CountableHilbertSum H) (y : K) :
    countableTensorIsometry
      ((x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K) = countableTensorVector x y := by
  exact LinearIsometry.fromCompletion_apply_coe _ _

theorem countableTensorIsometry_surjective :
    Function.Surjective (countableTensorIsometry (H := H) (K := K)) := by
  classical
  let J := countableTensorIsometry (H := H) (K := K)
  let V := J.toLinearMap.range
  have hV : IsClosed (V : Set (CountableHilbertSum (SpatialHilbert H K))) :=
    J.isometry.isClosedEmbedding.isClosed_range
  have hs (n : ℕ) (z : SpatialHilbert H K) : lp.single 2 n z ∈ V := by
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact hV.preimage (lp.isometry_single n).continuous
    | ih z =>
      induction z using TensorProduct.inductionOn with
      | add a b ha hb =>
        simpa only [UniformSpace.Completion.coe_add, lp.single_add] using V.add_mem ha hb
      | tmul x y =>
        refine ⟨((lp.single 2 n x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
          SpatialHilbert (CountableHilbertSum H) K), ?_⟩
        change countableTensorIsometry _ = _
        rw [countableTensorIsometry_tmul]
        ext m
        by_cases h : m = n
        · subst m; simp
        · simp [lp.single_apply, h]
  intro z
  have hz : z ∈ V := hV.mem_of_tendsto (lp.hasSum_single (by norm_num) z)
    (Filter.Eventually.of_forall fun s => V.sum_mem (fun n _ => hs n (z n)))
  exact hz

def countableTensorEquiv :
    SpatialHilbert (CountableHilbertSum H) K ≃ₗᵢ[ℂ]
      CountableHilbertSum (SpatialHilbert H K) :=
  LinearIsometryEquiv.ofSurjective countableTensorIsometry countableTensorIsometry_surjective

@[simp] theorem countableTensorEquiv_tmul (x : CountableHilbertSum H) (y : K) :
    countableTensorEquiv
      ((x ⊗ₜ[ℂ] y : CountableHilbertSum H ⊗[ℂ] K) :
        SpatialHilbert (CountableHilbertSum H) K) = countableTensorVector x y :=
  countableTensorIsometry_tmul x y

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Amplifying either tensor factor and then distributing gives the diagonal
amplification of its spatial action. -/
theorem countableTensorEquiv_intertwines (a : H →L[ℂ] H) (b : K →L[ℂ] K)
    (z : SpatialHilbert (CountableHilbertSum H) K) :
    countableTensorEquiv (spatialTensorOp (l2Diagonal a) b z) =
      l2Diagonal (spatialTensorOp a b) (countableTensorEquiv z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul x y =>
      simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, countableTensorEquiv_tmul]
      ext n
      simp only [countableTensorVector_apply, l2Diagonal_apply,
        spatialTensorOp_coe, TensorProduct.mapL_tmul]

end

end KadisonKastler

end OAI
