import OAI.Analysis.KadisonKastler.RegularCoreOperators
import OAI.Analysis.KadisonKastler.InfiniteCornerInflation
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

namespace OAI

/-! # Scalar Hilbert coordinates on the regular representation

A scalar Hilbert basis of `L²(ℝ)` gives an actual Hilbert direct-sum
decomposition of `L²(ℝ,H)`. Constant operators act on each summand by
their original action on `H`.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An elementary scalar-vector tensor, as a continuous bilinear map. -/
def regularTensorVector :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] H →L[ℂ] RegularCoreHilbert H :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip.compLpL₂
    2 (volume : Measure ℝ)).flip

omit [CompleteSpace H] in
theorem regularTensorVector_apply_ae (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularTensorVector f x =ᵐ[volume] fun t => f t • x :=
  (ContinuousLinearMap.toSpanSingleton ℂ x).coeFn_compLp f

omit [CompleteSpace H] in
theorem inner_regularTensorVector
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) :
    inner ℂ (regularTensorVector f x) (regularTensorVector g y) =
      inner ℂ f g * inner ℂ x y := by
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ t, inner ℂ (regularTensorVector f x t) (regularTensorVector g y t)) =
        ∫ t, inner ℂ (f t) (g t) * inner ℂ x y := by
      apply integral_congr_ae
      filter_upwards [regularTensorVector_apply_ae f x,
        regularTensorVector_apply_ae g y] with t hf hg
      rw [hf, hg]
      simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply, mul_assoc]
    _ = (∫ t, inner ℂ (f t) (g t)) * inner ℂ x y := integral_mul_const _ _

omit [CompleteSpace H] in
theorem norm_regularTensorVector
    (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    ‖regularTensorVector f x‖ = ‖f‖ * ‖x‖ := by
  have hsq : ‖regularTensorVector f x‖ ^ 2 = (‖f‖ * ‖x‖) ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_regularTensorVector,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp [pow_two]
    ring
  nlinarith [norm_nonneg (regularTensorVector f x), mul_nonneg (norm_nonneg f) (norm_nonneg x)]

variable {ι : Type*}

/-- The copy of `H` belonging to one scalar basis vector. -/
def regularBasisSummand (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (i : ι) : H →ₗᵢ[ℂ] RegularCoreHilbert H where
  __ := (regularTensorVector (b i)).toLinearMap
  norm_map' x := by
    change ‖regularTensorVector (b i) x‖ = ‖x‖
    rw [norm_regularTensorVector, b.orthonormal.norm_eq_one i, one_mul]

omit [CompleteSpace H] in
theorem regularBasisSummand_orthogonal
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    OrthogonalFamily ℂ (fun _ : ι => H) (regularBasisSummand b) := by
  intro i j hij x y
  change inner ℂ (regularTensorVector (b i) x) (regularTensorVector (b j) y) = 0
  rw [inner_regularTensorVector, b.orthonormal.inner_eq_zero hij, zero_mul]

omit [CompleteSpace H] in
theorem regularBasisSummand_total
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    ⊤ ≤ (⨆ i, LinearMap.range
      (regularBasisSummand (H := H) b i).toLinearMap).topologicalClosure := by
  let S : Submodule ℂ (RegularCoreHilbert H) :=
    ⨆ i, LinearMap.range (regularBasisSummand (H := H) b i).toLinearMap
  have hTensor (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
      regularTensorVector f x ∈ S.topologicalClosure := by
    have hsum := (regularTensorVector.flip x).hasSum (b.hasSum_repr f)
    apply S.isClosed_topologicalClosure.mem_of_tendsto hsum
    filter_upwards [] with s
    apply Submodule.le_topologicalClosure
    apply S.sum_mem
    intro i hi
    have hm : regularTensorVector (b i) x ∈ S :=
      (le_iSup (fun i => LinearMap.range
        (regularBasisSummand (H := H) b i).toLinearMap) i) ⟨x, rfl⟩
    simpa only [map_smul, ContinuousLinearMap.flip_apply] using S.smul_mem (b.repr f i) hm
  intro f hf
  clear hf
  change f ∈ S.topologicalClosure
  induction f using Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
  | @indicatorConst x s hs hfin =>
      have he : regularTensorVector (Lp.simpleFunc.indicatorConst 2 hs hfin.ne (1 : ℂ)) x =
          Lp.simpleFunc.indicatorConst 2 hs hfin.ne x := by
        apply Lp.ext
        filter_upwards [regularTensorVector_apply_ae
          (Lp.simpleFunc.indicatorConst 2 hs hfin.ne (1 : ℂ)) x,
          (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := (1 : ℂ))),
          (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin.ne) (c := x))]
            with t ht h1 hx
        rw [ht]
        change indicatorConstLp 2 hs hfin.ne (1 : ℂ) t • x =
          indicatorConstLp 2 hs hfin.ne x t
        rw [h1, hx]
        by_cases hts : t ∈ s <;> simp [hts]
      rw [← he]
      exact hTensor _ x
  | @add f g hf hg hdis hF hG => exact S.topologicalClosure.add_mem hF hG
  | isClosed => exact S.isClosed_topologicalClosure

/-- The regular space is the Hilbert sum of the scalar-basis copies of `H`. -/
theorem regularHilbertSum (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    IsHilbertSum ℂ (fun _ : ι => H) (regularBasisSummand b) :=
  IsHilbertSum.mk (regularBasisSummand_orthogonal b) (regularBasisSummand_total b)

/-- Actual Hilbert coordinates on the regular representation. -/
def regularHilbertCoordinates (b : HilbertBasis ι ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    RegularCoreHilbert H ≃ₗᵢ[ℂ] lp (fun _ : ι => H) 2 :=
  (regularHilbertSum b).linearIsometryEquiv

theorem regularConstantHom_tensorVector (T : H →L[ℂ] H)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularConstantHom (volume : Measure ℝ) T (regularTensorVector f x) =
      regularTensorVector f (T x) := by
  apply Lp.ext
  filter_upwards [regularConstantHom_apply_ae (volume : Measure ℝ) T
    (regularTensorVector f x), regularTensorVector_apply_ae f x,
    regularTensorVector_apply_ae f (T x)] with t ht hx hTx
  rw [ht, hx, hTx, map_smul]

/-- In scalar Hilbert coordinates, the constant operator is exactly the
coordinatewise operator. -/
theorem regularHilbertCoordinates_constant
    (b : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) (T : H →L[ℂ] H) :
    (regularHilbertCoordinates b).conjStarAlgEquiv
      (regularConstantHom (volume : Measure ℝ) T) = l2Diagonal T := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  intro i
  apply ContinuousLinearMap.ext
  intro x
  change regularHilbertCoordinates b (regularConstantHom (volume : Measure ℝ) T
      ((regularHilbertCoordinates b).symm (lp.single 2 i x))) =
    l2Diagonal T (lp.single 2 i x)
  have hs (y : H) : (regularHilbertCoordinates b).symm (lp.single 2 i y) =
      regularTensorVector (b i) y :=
    (regularHilbertSum b).linearIsometryEquiv_symm_apply_single y
  rw [hs, regularConstantHom_tensorVector, l2Diagonal_single, ← hs]
  exact (regularHilbertCoordinates b).apply_symm_apply _

end

end KadisonKastler

end OAI
