import Mathlib
import OAI.Analysis.AffineBernstein.CompactIntegration

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section DeterminantVariation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Jacobi's formula without assuming invertibility of the varied matrix. -/
theorem hasDerivAt_det_line (A B : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (A + t • B).det)
      (∑ i, ∑ j, A.adjugate j i * B i j) 0 := by
  have hline := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (fun i j => B i j)).const_add
    (fun i j => A i j)
  have hc := (((continuousDetRows (ι := ι)).hasFDerivAt
    ((fun i j => A i j) + (0 : ℝ) • (fun i j => B i j))).comp 0 hline).hasDerivAt
  simp only [zero_smul, add_zero, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul] at hc
  have hd : continuousDetRows.linearDeriv (fun i j => A i j) (fun i j => B i j) =
      ∑ i, ∑ j, A.adjugate j i * B i j := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    apply Finset.sum_congr rfl
    intro i hi
    change (A.updateRow i (B i)).det = _
    rw [det_updateRow_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Matrix.adjugate_apply, mul_comm]
  rw [hd] at hc
  exact hc

/-- Pointwise first variation of the actual affine-area density. -/
theorem hasDerivAt_affineArea_matrix (A B : Matrix ι ι ℝ) (hA : A.PosDef) (δ : ℝ) :
    HasDerivAt (fun t : ℝ => Real.rpow (A + t • B).det δ)
      (δ * Real.rpow A.det (δ - 1) * (∑ i, ∑ j, A.adjugate j i * B i j)) 0 := by
  have hd := (hasDerivAt_det_line A B).rpow_const (p := δ) (Or.inl (by simpa using ne_of_gt hA.det_pos))
  simp only [zero_smul, add_zero] at hd
  simp only [Real.rpow_eq_pow]
  convert hd using 1
  ring

end DeterminantVariation

section RadialCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Away from topological support the test is locally zero, so no extension
of a smooth coefficient across the original boundary is necessary. -/
theorem contDiff_of_contDiffAt_tsupport {f : E → ℝ} {k : ℕ∞ω}
    (hf : ∀ x ∈ tsupport f, ContDiffAt ℝ k f x) : ContDiff ℝ k f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf x hx
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hx)

/-- Commuting fixed-direction differentiation with evaluation of a derivative. -/
theorem dirDeriv_eq_second {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = fderiv ℝ (fderiv ℝ f) x v z := by
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply (hasFDerivAt_const z x)
  change fderiv ℝ (fun y => fderiv ℝ f y z) x v = _
  rw [he.fderiv]
  simp

/-- Symmetry of the second derivative in fixed directions. -/
theorem dirDeriv_comm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x) (v z : E) :
    dirDeriv v (dirDeriv z f) x = dirDeriv z (dirDeriv v f) x := by
  rw [dirDeriv_eq_second hf, dirDeriv_eq_second hf]
  exact hf.isSymmSndFDerivAt (by simp) v z

/-- The support-plane height `ν(o-X)` in original graph coordinates. -/
def radialSupport (u : E → ℝ) (o : E) (c : ℝ) (x : E) : ℝ :=
  c - u x + fderiv ℝ u x (x - o)

/-- Smoothness holds only locally; the eventual zero argument handles tests. -/
theorem contDiffAt_radialSupport {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (o : E) (c : ℝ) :
    ContDiffAt ℝ ∞ (radialSupport u o c) x :=
  (contDiffAt_const.sub hu).add
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply (contDiffAt_id.sub contDiffAt_const))

/-- The derivative of the radial gradient, including its moving vector argument. -/
theorem dirDeriv_radialGradient {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (o v : E) :
    dirDeriv v (fun y => fderiv ℝ u y (y - o)) x =
      dirDeriv (x - o) (dirDeriv v u) x + dirDeriv v u x := by
  have hd := ((hu.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := hd.clm_apply ((hasFDerivAt_id x).sub_const o)
  simp only [id_eq] at he
  unfold dirDeriv
  rw [he.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.id_apply]
  rw [← dirDeriv_eq_second hu v (x - o), dirDeriv_comm hu v (x - o)]
  exact add_comm _ _

/-- The cancellation `D Z = H(x-o)` with no coordinate or global extension assumption. -/
theorem dirDeriv_radialSupport {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (o : E) (c : ℝ) (v : E) :
    dirDeriv v (radialSupport u o c) x = dirDeriv (x - o) (dirDeriv v u) x := by
  have hdu := hu.differentiableAt (by simp)
  have hdr : DifferentiableAt ℝ (fun y => fderiv ℝ u y (y - o)) x :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_id.sub (contDiffAt_const (c := o)))).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => c - u y) x := by fun_prop
  unfold radialSupport dirDeriv
  rw [fderiv_fun_add hs hdr, fderiv_const_sub]
  simp only [add_apply]
  rw [show fderiv ℝ (fun y => fderiv ℝ u y (y - o)) x v =
      dirDeriv (x - o) (dirDeriv v u) x + dirDeriv v u x from
        dirDeriv_radialGradient hu o v]
  simp only [dirDeriv, neg_apply]
  ring_nf
  rfl

/-- The exact second derivative of the support-plane height. -/
theorem second_dirDeriv_radialSupport {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : E} (hx : x ∈ Ω)
    (o : E) (c : ℝ) (v z : E) :
    dirDeriv z (dirDeriv v (radialSupport u o c)) x =
      dirDeriv z (dirDeriv v u) x +
        dirDeriv (x - o) (dirDeriv z (dirDeriv v u)) x := by
  have he : dirDeriv v (radialSupport u o c) =ᶠ[nhds x]
      (fun y => fderiv ℝ (dirDeriv v u) y (y - o)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_radialSupport (hu.contDiffAt (hΩ.mem_nhds hy)) o c v
  change fderiv ℝ _ x z = _
  rw [he.fderiv_eq]
  exact (dirDeriv_radialGradient
    (contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) v) o z).trans (add_comm _ _)

end RadialCalculus

/-- The coordinate version used in the trace of the cap test. -/
theorem hessian_radialSupport {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (o : Space n) (c : ℝ) (i j : Fin n) :
    hessian (radialSupport u o c) x i j = hessian u x i j +
      dirDeriv (x - o) (fun y => hessian u y i j) x :=
  second_dirDeriv_radialSupport hΩ hu hx o c (coordinateVector n j) (coordinateVector n i)

/-- Jacobi's formula in arbitrary fixed directions, for the actual entries. -/
theorem dirDeriv_det {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] (A : E → Matrix ι ι ℝ) {x : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (v : E) :
    dirDeriv v (fun y => (A y).det) x =
      ∑ i, ∑ j, (A x).adjugate j i * dirDeriv v (fun y => A y i j) x := by
  let D : E →L[ℝ] (ι → ι → ℝ) := ContinuousLinearMap.pi fun i =>
    ContinuousLinearMap.pi fun j => fderiv ℝ (fun y => A y i j) x
  have hD : HasFDerivAt (fun y i j => A y i j) D x :=
    hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j => (hA i j).hasFDerivAt
  have hc := (continuousDetRows.hasFDerivAt (fun i j => A x i j)).comp x hD
  change fderiv ℝ (continuousDetRows ∘ (fun y i j => A y i j)) x v = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change ((A x).updateRow i (fun j => dirDeriv v (fun y => A y i j) x)).det = _
  rw [det_updateRow_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Matrix.adjugate_apply, mul_comm]

/-- Smoothness of the area density on the original domain. -/
theorem contDiffAt_affineAreaDensity {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) :
    ContDiffAt ℝ ∞ (affineAreaDensity u) x :=
  (contDiffAt_det_hessian hu).rpow_const_of_ne (ne_of_gt hpos.det_pos)

/-- The exact differential of the affine area coefficient. -/
theorem dirDeriv_affineAreaDensity {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef) (v : Space n) :
    dirDeriv v (affineAreaDensity u) x =
      (1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv v (fun y => hessian u y i j) x) := by
  have hd := ((contDiffAt_det_hessian hu).differentiableAt (by simp)).hasFDerivAt
  have hr := hd.rpow_const (p := 1 / ((n : ℝ) + 2)) (Or.inl (ne_of_gt hpos.det_pos))
  have he : (1 / ((n : ℝ) + 2)) - 1 = -(((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    field_simp
    ring
  have hc : dirDeriv v (affineAreaDensity u) x =
      (1 / ((n : ℝ) + 2)) * affineWeight u x *
        dirDeriv v (fun y => (hessian u y).det) x := by
    unfold dirDeriv affineAreaDensity
    simp only [Real.rpow_eq_pow]
    rw [hr.fderiv]
    simp only [smul_apply, smul_eq_mul, he, affineWeight, Real.rpow_eq_pow]
  rw [hc, dirDeriv_det (hessian u)
    (fun i j => (contDiffAt_hessian_entry hu i j).differentiableAt (by simp))]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hcof : (hessian u x).adjugate j i = cofactorHessian u x i j := by
    rw [← cofactorHessian_eq_adjugate u x (ne_of_gt hpos.det_pos)]
    exact (cofactorHessian_isSymm u x hpos).apply i j
  rw [hcof]
  calc
    _ = (1 / ((n : ℝ) + 2)) * (affineWeight u x * cofactorHessian u x i j) *
        dirDeriv v (fun y => hessian u y i j) x := by ring
    _ = _ := by rw [affine_weight_cofactor_entry hpos]; ring

/-- Trace of the identity, in the entry convention used in the manuscript. -/
theorem trace_inverse_mul_self {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) : (∑ i, ∑ j, H⁻¹ i j * H i j) = (n : ℝ) := by
  have hs := Matrix.isHermitian_iff_isSymm.mp hH.isHermitian
  have he : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos))
  calc
    _ = ∑ i, (H⁻¹ * H) i i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hs.apply i j]
    _ = n := by rw [he]; simp

/-- Weighted radial trace, avoiding a logarithm at points outside the domain. -/
theorem weighted_trace_radialSupport {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hpos : (hessian u x).PosDef)
    (o : Space n) (c : ℝ) :
    affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (radialSupport u o c) x i j) =
        n * affineAreaDensity u x + ((n : ℝ) + 2) * dirDeriv (x - o) (affineAreaDensity u) x := by
  simp_rw [hessian_radialSupport hΩ hu hx o c, mul_add, Finset.sum_add_distrib]
  rw [trace_inverse_mul_self hpos,
    dirDeriv_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds hx)) hpos]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- Expansion in the frozen Euclidean coordinate vectors. -/
theorem sum_coordinateVector {n : ℕ} (v : Space n) :
    (∑ i, (v i) • coordinateVector n i) = v := by
  ext j
  simp [coordinateVector, Pi.single_apply]

/-- Linear functionals are recovered exactly by coordinates. -/
theorem clm_coordinate_sum {n : ℕ} (L : Space n →L[ℝ] ℝ) (v : Space n) :
    L v = ∑ i, v i * L (coordinateVector n i) := by
  conv_lhs => rw [← sum_coordinateVector v]
  simp

/-- The radial vector derivative is the sum of its coordinate derivatives. -/
theorem dirDeriv_coordinate_sum {n : ℕ} (f : Space n → ℝ) (x v : Space n) :
    dirDeriv v f x = ∑ i, v i * dirDeriv (coordinateVector n i) f x :=
  clm_coordinate_sum (fderiv ℝ f x) v

/-- A second derivative product rule on the actual open domain. -/
theorem second_dirDeriv_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : E} (hx : x ∈ Ω) (v z : E) :
    dirDeriv z (dirDeriv v (fun y => f y * g y)) x =
      dirDeriv z (dirDeriv v f) x * g x + dirDeriv v f x * dirDeriv z g x +
      dirDeriv z f x * dirDeriv v g x + f x * dirDeriv z (dirDeriv v g) x := by
  have he : dirDeriv v (fun y => f y * g y) =ᶠ[nhds x]
      (fun y => dirDeriv v f y * g y + f y * dirDeriv v g y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_mul ((hf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) v
  have hfx := hf.contDiffAt (hΩ.mem_nhds hx)
  have hgx := hg.contDiffAt (hΩ.mem_nhds hx)
  have hdf := hfx.differentiableAt (by simp)
  have hdg := hgx.differentiableAt (by simp)
  have hdfv := (contDiffAt_dirDeriv hfx v).differentiableAt (by simp)
  have hdgv := (contDiffAt_dirDeriv hgx v).differentiableAt (by simp)
  change fderiv ℝ _ x z = _
  have h1 : DifferentiableAt ℝ (fun y => dirDeriv v f y * g y) x := hdfv.mul hdg
  have h2 : DifferentiableAt ℝ (fun y => f y * dirDeriv v g y) x := hdf.mul hdgv
  rw [he.fderiv_eq, fderiv_fun_add h1 h2]
  simp only [add_apply]
  change dirDeriv z (fun y => dirDeriv v f y * g y) x +
    dirDeriv z (fun y => f y * dirDeriv v g y) x = _
  rw [dirDeriv_mul hdfv hdg, dirDeriv_mul hdf hdgv]
  ring

/-- Scalar composition by its actual one-dimensional derivative. -/
theorem dirDeriv_comp_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E → ℝ} {ψ : ℝ → ℝ} {x : E} (hq : DifferentiableAt ℝ q x)
    (hψ : DifferentiableAt ℝ ψ (q x)) (v : E) :
    dirDeriv v (fun y => ψ (q y)) x = deriv ψ (q x) * dirDeriv v q x := by
  have hd := hψ.hasDerivAt.comp_hasFDerivAt x hq.hasFDerivAt
  change fderiv ℝ (ψ ∘ q) x v = _
  rw [hd.fderiv]
  rfl

/-- The second chain rule used by a cap test. -/
theorem second_dirDeriv_comp_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {q : E → ℝ} {ψ : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω) (hψ : ContDiff ℝ ∞ ψ)
    {x : E} (hx : x ∈ Ω) (v z : E) :
    dirDeriv z (dirDeriv v (fun y => ψ (q y))) x =
      deriv (deriv ψ) (q x) * dirDeriv z q x * dirDeriv v q x +
      deriv ψ (q x) * dirDeriv z (dirDeriv v q) x := by
  have hψ' : ContDiff ℝ ∞ (deriv ψ) := hψ.deriv'
  have he : dirDeriv v (fun y => ψ (q y)) =ᶠ[nhds x]
      (fun y => deriv ψ (q y) * dirDeriv v q y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_comp_scalar ((hq.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      (hψ.differentiable (by simp) (q y)) v
  have hqx := hq.contDiffAt (hΩ.mem_nhds hx)
  have hdq := hqx.differentiableAt (by simp)
  change fderiv ℝ _ x z = _
  rw [he.fderiv_eq]
  change dirDeriv z (fun y => deriv ψ (q y) * dirDeriv v q y) x = _
  have hdc : DifferentiableAt ℝ (fun y => deriv ψ (q y)) x :=
    (hψ'.contDiffAt.comp x hqx).differentiableAt (by simp)
  rw [dirDeriv_mul hdc
    ((contDiffAt_dirDeriv hqx v).differentiableAt (by simp)),
    dirDeriv_comp_scalar hdq (hψ'.differentiable (by simp) (q x))]

/-- Restriction of an arbitrary ambient affine function to the original graph. -/
def graphAffineFunction {n : ℕ} (u : Space n → ℝ) (a : Space n →L[ℝ] ℝ)
    (b d : ℝ) (x : Space n) : ℝ := a x + b * u x + d

theorem contDiffAt_graphAffineFunction {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    ContDiffAt ℝ ∞ (graphAffineFunction u a b d) x := by
  exact (a.contDiff.contDiffAt.add (contDiffAt_const.mul hu)).add contDiffAt_const

theorem dirDeriv_graphAffineFunction {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) (a : Space n →L[ℝ] ℝ) (b d : ℝ) (v : Space n) :
    dirDeriv v (graphAffineFunction u a b d) x = a v + b * dirDeriv v u x := by
  unfold dirDeriv graphAffineFunction
  rw [fderiv_add_const, fderiv_fun_add a.differentiableAt (hu.const_mul b),
    fderiv_const_mul hu]
  simp

theorem hessian_graphAffineFunction {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) (i j : Fin n) :
    hessian (graphAffineFunction u a b d) x i j = b * hessian u x i j := by
  have he : dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) =ᶠ[nhds x]
      (fun y => a (coordinateVector n j) + b * dirDeriv (coordinateVector n j) u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact dirDeriv_graphAffineFunction
      ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) a b d _
  change fderiv ℝ (dirDeriv (coordinateVector n j) (graphAffineFunction u a b d)) x
    (coordinateVector n i) = _
  rw [he.fderiv_eq, fderiv_const_add,
    fderiv_const_mul ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx))
      (coordinateVector n j)).differentiableAt (by simp))]
  rfl

/-- Coordinate pairing equals the ordinary matrix-vector contraction. -/
theorem matrix_pair_eq_dot {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (p q : ι → ℝ) :
    (∑ i, ∑ j, A i j * p i * q j) = p ⬝ᵥ (A.mulVec q) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Symmetry of the covector contraction, with the literal matrix coefficients. -/
theorem matrix_pair_symm {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsSymm) (p q : ι → ℝ) :
    (∑ i, ∑ j, A i j * p i * q j) = ∑ i, ∑ j, A i j * q i * p j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.apply i j]
  ring

/-- Exact inverse contraction for a radial vector and a covector. -/
theorem inverse_radial_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (v p : ι → ℝ) :
    (∑ i, ∑ j, H⁻¹ i j * (∑ k, v k * H k i) * p j) = ∑ i, v i * p i := by
  rw [matrix_pair_eq_dot]
  change (Matrix.vecMul v H) ⬝ᵥ ((H⁻¹).mulVec p) = _
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr (ne_of_gt hH.det_pos)), Matrix.vecMul_one]
  rfl

/-- The radial support gradient cancels exactly against the inverse Hessian. -/
theorem inverseHessian_radialSupport {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hpos : (hessian u x).PosDef)
    (o : Space n) (c : ℝ) (q : Space n → ℝ) :
    (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      dirDeriv (coordinateVector n i) (radialSupport u o c) x *
      dirDeriv (coordinateVector n j) q x) = dirDeriv (x - o) q x := by
  simp_rw [dirDeriv_radialSupport hu o c]
  have he (i : Fin n) : dirDeriv (x - o) (dirDeriv (coordinateVector n i) u) x =
      ∑ k, (x - o) k * hessian u x k i :=
    dirDeriv_coordinate_sum (dirDeriv (coordinateVector n i) u) x (x - o)
  simp_rw [he]
  rw [inverse_radial_contraction hpos]
  exact (dirDeriv_coordinate_sum q x (x - o)).symm

/-- Product trace in coordinates. -/
theorem hessian_product_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f g : Space n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω)
    {x : Space n} (hx : x ∈ Ω) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    (∑ i, ∑ j, A i j * hessian (fun y => f y * g y) x i j) =
      g x * (∑ i, ∑ j, A i j * hessian f x i j) +
      f x * (∑ i, ∑ j, A i j * hessian g x i j) +
      2 * (∑ i, ∑ j, A i j * dirDeriv (coordinateVector n i) f x *
        dirDeriv (coordinateVector n j) g x) := by
  have he (i j : Fin n) : hessian (fun y => f y * g y) x i j =
      hessian f x i j * g x + dirDeriv (coordinateVector n j) f x *
        dirDeriv (coordinateVector n i) g x +
      dirDeriv (coordinateVector n i) f x * dirDeriv (coordinateVector n j) g x +
      f x * hessian g x i j :=
    second_dirDeriv_mul hΩ hf hg hx (coordinateVector n j) (coordinateVector n i)
  simp_rw [he, mul_add, Finset.sum_add_distrib]
  have hswap := matrix_pair_symm hA
    (fun i => dirDeriv (coordinateVector n i) f x)
    (fun i => dirDeriv (coordinateVector n i) g x)
  have hterm1 : (∑ i, ∑ j, A i j * (hessian f x i j * g x)) =
      g x * (∑ i, ∑ j, A i j * hessian f x i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hterm2 : (∑ i, ∑ j, A i j * (f x * hessian g x i j)) =
      f x * (∑ i, ∑ j, A i j * hessian g x i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hterm3 : (∑ i, ∑ j, A i j *
      (dirDeriv (coordinateVector n j) f x * dirDeriv (coordinateVector n i) g x)) =
      ∑ i, ∑ j, A i j * dirDeriv (coordinateVector n i) f x *
        dirDeriv (coordinateVector n j) g x := by
    rw [hswap]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hterm1, hterm2, hterm3]
  simp only [← mul_assoc]
  ring

/-- Chain trace in coordinates. -/
theorem hessian_composition_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {q : Space n → ℝ} {ψ : ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q Ω) (hψ : ContDiff ℝ ∞ ψ)
    {x : Space n} (hx : x ∈ Ω) (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, A i j * hessian (fun y => ψ (q y)) x i j) =
      deriv (deriv ψ) (q x) * (∑ i, ∑ j, A i j *
        dirDeriv (coordinateVector n i) q x * dirDeriv (coordinateVector n j) q x) +
      deriv ψ (q x) * (∑ i, ∑ j, A i j * hessian q x i j) := by
  have he (i j : Fin n) : hessian (fun y => ψ (q y)) x i j =
      deriv (deriv ψ) (q x) * dirDeriv (coordinateVector n i) q x *
        dirDeriv (coordinateVector n j) q x + deriv ψ (q x) * hessian q x i j :=
    second_dirDeriv_comp_scalar hΩ hq hψ hx (coordinateVector n j) (coordinateVector n i)
  simp_rw [he, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- Positivity fixes the inverse-Hessian symmetry employed in a cap test. -/
theorem inverseHessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hpos : (hessian u x).PosDef) : ((hessian u x)⁻¹).IsSymm :=
  (Matrix.isHermitian_iff_isSymm.mp hpos.isHermitian).inv

/-- Pointwise first-variation integrand of the source cap test. -/
theorem weighted_trace_capTest {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) {x : Space n} (hx : x ∈ Ω)
    (hpos : (hessian u x).PosDef) (o : Space n) (c : ℝ)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    let q := graphAffineFunction u a b d
    let Z := radialSupport u o c
    affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (fun y => Z y * ψ (q y)) x i j) =
    affineAreaDensity u x *
      (Z x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv (coordinateVector n i) q x *
        dirDeriv (coordinateVector n j) q x) * deriv (deriv ψ) (q x) +
       n * Z x * b * deriv ψ (q x) + 2 * dirDeriv (x - o) q x * deriv ψ (q x) +
       n * ψ (q x)) +
    ((n : ℝ) + 2) * ψ (q x) * dirDeriv (x - o) (affineAreaDensity u) x := by
  dsimp only
  let q := graphAffineFunction u a b d
  let Z := radialSupport u o c
  have hq : ContDiffOn ℝ ∞ q Ω := fun y hy =>
    (contDiffAt_graphAffineFunction (hu.contDiffAt (hΩ.mem_nhds hy)) a b d).contDiffWithinAt
  have hZ : ContDiffOn ℝ ∞ Z Ω := fun y hy =>
    (contDiffAt_radialSupport (hu.contDiffAt (hΩ.mem_nhds hy)) o c).contDiffWithinAt
  have hψq : ContDiffOn ℝ ∞ (fun y => ψ (q y)) Ω :=
    hψ.comp_contDiffOn hq
  have htraceq : (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian q x i j) = n * b := by
    dsimp only [q]
    simp_rw [hessian_graphAffineFunction hΩ hu hx a b d]
    calc
      _ = b * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian u x i j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = n * b := by rw [trace_inverse_mul_self hpos, mul_comm]
  have hcross : (∑ i, ∑ j, (hessian u x)⁻¹ i j * dirDeriv (coordinateVector n i) Z x *
      dirDeriv (coordinateVector n j) (fun y => ψ (q y)) x) =
        deriv ψ (q x) * dirDeriv (x - o) q x := by
    simp_rw [dirDeriv_comp_scalar ((hq.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
      (hψ.differentiable (by simp) (q x))]
    calc
      _ = deriv ψ (q x) * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) Z x * dirDeriv (coordinateVector n j) q x) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [inverseHessian_radialSupport (hu.contDiffAt (hΩ.mem_nhds hx)) hpos]
  change affineAreaDensity u x *
    (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (fun y => Z y * ψ (q y)) x i j) = _
  rw [hessian_product_trace hΩ hZ hψq hx (inverseHessian_isSymm hpos),
    hessian_composition_trace hΩ hq hψ hx, htraceq, hcross]
  have hrad := weighted_trace_radialSupport hΩ hu hx hpos o c
  change affineAreaDensity u x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian Z x i j) = _ at hrad
  linear_combination ψ (q x) * hrad

/-- Cancellation of the affine coefficients in the first variation. -/
theorem cap_affine_cancellation {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : DifferentiableAt ℝ u x) (o : Space n) (c : ℝ)
    (a : Space n →L[ℝ] ℝ) (b d : ℝ) :
    radialSupport u o c x * b - dirDeriv (x - o) (graphAffineFunction u a b d) x =
      (a o + b * c + d) - graphAffineFunction u a b d x := by
  rw [dirDeriv_graphAffineFunction hu]
  simp only [radialSupport, graphAffineFunction, dirDeriv, map_sub]
  ring

/-- The actual coordinate functional through the Euclidean-space equivalence. -/
def coordinateProjection (n : ℕ) (i : Fin n) : Space n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

@[simp] theorem coordinateProjection_apply (n : ℕ) (i : Fin n) (x : Space n) :
    coordinateProjection n i x = x i := rfl

/-- A smooth compact test makes a merely locally smooth coefficient globally smooth. -/
theorem contDiff_mul_at_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {k : ℕ∞ω} (hg : ContDiff ℝ k g)
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ k f x) :
    ContDiff ℝ k (fun x => f x * g x) := by
  apply contDiff_of_contDiffAt_tsupport
  intro x hx
  exact (hf x (tsupport_mul_subset_right hx)).mul hg.contDiffAt

/-- Integral of a derivative of a smooth compactly supported scalar field. -/
theorem integral_dirDeriv_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (v : E) :
    (∫ x, dirDeriv v f x ∂μ) = 0 := by
  have he := integral_mul_fderiv_compact (μ := μ) (fun _ : E => (1 : ℝ)) f v
    (fun _ _ => contDiffAt_const)
    (hf.of_le (by simp)) hfc
  simpa [dirDeriv] using he

/-- Radial integration by parts with a compact test and no global extension of `f`.
This formulation gives integrability as well as the identity. -/
theorem integral_radial_divergence_compact {n : ℕ}
    {μ : Measure (Space n)} [μ.IsAddHaarMeasure]
    (f σ : Space n → ℝ) (o : Space n)
    (hσ : ContDiff ℝ ∞ σ) (hσc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x) :
    let D := fun x => dirDeriv (x - o) f x * σ x +
      f x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x)
    Integrable D μ ∧ (∫ x, D x ∂μ) = 0 := by
  dsimp only
  let G (i : Fin n) (x : Space n) : ℝ := (x i - o i) * σ x
  let F (i : Fin n) (x : Space n) : ℝ := f x * G i x
  have hG (i : Fin n) : ContDiff ℝ ∞ (G i) := by
    exact ((coordinateProjection n i).contDiff.sub contDiff_const).mul hσ
  have hsG (i : Fin n) : tsupport (G i) ⊆ tsupport σ := tsupport_mul_subset_right
  have hsF (i : Fin n) : tsupport (F i) ⊆ tsupport σ :=
    tsupport_mul_subset_right.trans (hsG i)
  have hFc (i : Fin n) : HasCompactSupport (F i) :=
    hσc.of_isClosed_subset (isClosed_tsupport _) (hsF i)
  have hF (i : Fin n) : ContDiff ℝ ∞ (F i) :=
    contDiff_mul_at_tsupport (hG i) (fun x hx => hf x (hsG i hx))
  have hcoord (i : Fin n) (x : Space n) :
      dirDeriv (coordinateVector n i) (fun y : Space n => y i - o i) x = 1 := by
    change fderiv ℝ (fun y => coordinateProjection n i y - o i) x (coordinateVector n i) = 1
    rw [fderiv_sub_const, (coordinateProjection n i).fderiv]
    simp [coordinateVector]
  have hderiv (i : Fin n) (x : Space n) :
      dirDeriv (coordinateVector n i) (F i) x =
        dirDeriv (coordinateVector n i) f x * (x i - o i) * σ x +
        f x * (σ x + (x i - o i) * dirDeriv (coordinateVector n i) σ x) := by
    by_cases hx : x ∈ tsupport σ
    · have hdf := (hf x hx).differentiableAt (by simp)
      have hdc : DifferentiableAt ℝ (fun y : Space n => y i - o i) x :=
        ((coordinateProjection n i).differentiableAt.sub_const (o i))
      change dirDeriv (coordinateVector n i) (fun y => f y * G i y) x = _
      rw [dirDeriv_mul hdf ((hG i).differentiable (by simp) x)]
      change dirDeriv (coordinateVector n i) f x * ((x i - o i) * σ x) +
        f x * dirDeriv (coordinateVector n i) (fun y => (y i - o i) * σ y) x = _
      rw [dirDeriv_mul hdc (hσ.differentiable (by simp) x), hcoord]
      ring
    · have hz : σ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hz' : dirDeriv (coordinateVector n i) σ x = 0 := by
        unfold dirDeriv
        rw [fderiv_of_notMem_tsupport ℝ hx]
        rfl
      have hFz : dirDeriv (coordinateVector n i) (F i) x = 0 := by
        unfold dirDeriv
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hsF i h))]
        rfl
      rw [hz, hz', hFz]
      ring
  have hi (i : Fin n) : Integrable (dirDeriv (coordinateVector n i) (F i)) μ :=
    integrable_of_support_subset_compact (hFc i).isCompact
      ((subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _))
      (contDiff_dirDeriv (hF i) _).continuous.continuousOn
  have he (x : Space n) :
      dirDeriv (x - o) f x * σ x + f x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x) =
        ∑ i, dirDeriv (coordinateVector n i) (F i) x := by
    simp_rw [hderiv]
    rw [dirDeriv_coordinate_sum f x (x - o), dirDeriv_coordinate_sum σ x (x - o)]
    simp only [PiLp.sub_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    have hsum : (∑ i, (x i - o i) * dirDeriv (coordinateVector n i) f x * σ x) =
        ∑ i, dirDeriv (coordinateVector n i) f x * (x i - o i) * σ x := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hall : (fun x => dirDeriv (x - o) f x * σ x +
      f x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x)) =
      (fun x => ∑ i, dirDeriv (coordinateVector n i) (F i) x) := funext he
  rw [hall]
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_dirDeriv_compact _ (hF _) (hFc _)]
  simp

/-- Zero-extension of a compactly supported local test is genuinely smooth on the
ambient coordinate space; no extension theorem for the graph is needed. -/
theorem contDiff_indicator_of_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {f : E → ℝ} {k : ℕ∞ω} (hf : ContDiffOn ℝ k f Ω)
    (hz : ∀ x ∈ Ω, x ∉ K → f x = 0) :
    ContDiff ℝ k (Ω.indicator f) ∧ HasCompactSupport (Ω.indicator f) ∧
      tsupport (Ω.indicator f) ⊆ K := by
  have hs : Function.support (Ω.indicator f) ⊆ K := by
    intro x hx
    by_contra hxK
    by_cases hxΩ : x ∈ Ω
    · exact hx (by rw [Set.indicator_of_mem hxΩ, hz x hxΩ hxK])
    · exact hx (Set.indicator_of_notMem hxΩ f)
  have ht : tsupport (Ω.indicator f) ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩
  apply contDiff_of_contDiffAt_tsupport
  intro x hx
  have hxΩ := hKΩ (ht hx)
  apply (hf.contDiffAt (hΩ.mem_nhds hxΩ)).congr_of_eventuallyEq
  filter_upwards [hΩ.mem_nhds hxΩ] with y hy
  exact Set.indicator_of_mem hy f

/-- Hessians depend only on the germ of a function, also with the total derivative
convention at points outside the domain. -/
theorem hessian_eq_of_eventuallyEq {n : ℕ} {f g : Space n → ℝ} {x : Space n}
    (h : f =ᶠ[nhds x] g) : hessian f x = hessian g x := by
  ext i j
  have h' : (fun y => fderiv ℝ f y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ g y (coordinateVector n j)) :=
    (h.fderiv (𝕜 := ℝ)).mono fun y hy => congrArg (fun L => L (coordinateVector n j)) hy
  exact congrArg (fun L : Space n →L[ℝ] ℝ => L (coordinateVector n i)) h'.fderiv_eq

/-- The actual first-variation density is integrable for a compact local test. -/
theorem integrableOn_area_variation {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) :
    IntegrableOn (fun x => affineAreaDensity u x *
      (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) Ω := by
  have hi (i j : Fin n) : Integrable (fun x =>
      affineWeight u x * cofactorHessian u x i j * hessian η x i j) := by
    apply integrable_of_support_subset_compact hηc.isCompact
    · exact (Function.support_mul_subset_right _ _).trans
        ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ _).trans
          (tsupport_fderiv_apply_subset ℝ _)))
    · intro x hx
      have hc := (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds (hηΩ hx)))
        (hpos x (hηΩ hx))).mul
          (contDiffAt_cofactorHessian_entry hΩ hu hpos (hηΩ hx) i j)
      exact (hc.mul (contDiffAt_hessian_entry hη.contDiffAt i j)).continuousAt.continuousWithinAt
  have hiSum := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))
  apply hiSum.integrableOn.congr_fun _ hΩ.measurableSet
  intro x hx
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [affine_weight_cofactor_entry (hpos x hx), mul_assoc]

/-- The cap identity in the original graph coordinates (source `area.tex`,
Lemma Cap identity). The source assumes compact support of all three displayed
scalar compositions; this proof in fact only needs the first support condition.
The measure here is precisely affine area density times Lebesgue measure. -/
theorem affineMaximal_graph_cap_identity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (o : Space n) (c : ℝ) (a : Space n →L[ℝ] ℝ) (b d : ℝ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {K : Set (Space n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hsupport : ∀ x ∈ Ω, x ∉ K → ψ (graphAffineFunction u a b d x) = 0) :
    (∫ x in Ω, affineAreaDensity u x *
      (radialSupport u o c x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) (graphAffineFunction u a b d) x *
          dirDeriv (coordinateVector n j) (graphAffineFunction u a b d) x) *
            deriv (deriv ψ) (graphAffineFunction u a b d x) +
       (n : ℝ) * ((a o + b * c + d) - graphAffineFunction u a b d x) *
         deriv ψ (graphAffineFunction u a b d x) -
       (n : ℝ) * ((n : ℝ) + 1) * ψ (graphAffineFunction u a b d x))) = 0 := by
  let q := graphAffineFunction u a b d
  let Z := radialSupport u o c
  let ρ := affineAreaDensity u
  let σ := Ω.indicator (fun x => ψ (q x))
  let η := fun x => Z x * σ x
  let F := fun x => ρ x * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)
  let D := fun x => dirDeriv (x - o) ρ x * σ x +
    ρ x * ((n : ℝ) * σ x + dirDeriv (x - o) σ x)
  have hq : ContDiffOn ℝ ∞ q Ω := fun x hx =>
    (contDiffAt_graphAffineFunction (hu.contDiffAt (hΩ.mem_nhds hx)) a b d).contDiffWithinAt
  have hσpack := contDiff_indicator_of_compact hΩ hK hKΩ (hψ.comp_contDiffOn hq) hsupport
  have hσ : ContDiff ℝ ∞ σ := hσpack.1
  have hσc : HasCompactSupport σ := hσpack.2.1
  have hσΩ : tsupport σ ⊆ Ω := hσpack.2.2.trans hKΩ
  have hηs : tsupport η ⊆ tsupport σ := tsupport_mul_subset_right
  have hη : ContDiff ℝ ∞ η := contDiff_mul_at_tsupport hσ fun x hx =>
    contDiffAt_radialSupport (hu.contDiffAt (hΩ.mem_nhds (hσΩ hx))) o c
  have hηc : HasCompactSupport η := hσc.of_isClosed_subset (isClosed_tsupport _) hηs
  have hηΩ := hηs.trans hσΩ
  have hFint : IntegrableOn F Ω := integrableOn_area_variation hΩ hu hpos η hη hηc hηΩ
  have hFzero : (∫ x in Ω, F x) = 0 :=
    affineMaximal_area_stationarity hΩ hu hpos hmax η hη hηc hηΩ
  have hDpack : Integrable D ∧ (∫ x, D x) = 0 :=
    integral_radial_divergence_compact ρ σ o hσ hσc fun x hx =>
      contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hσΩ hx))) (hpos x (hσΩ hx))
  have hDzero : (∫ x in Ω, D x) = 0 := by
    calc
      _ = ∫ x, D x := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hn : x ∉ tsupport σ := fun h => hx (hσΩ h)
        have hσ0 : σ x = 0 := image_eq_zero_of_notMem_tsupport hn
        have hσ1 : dirDeriv (x - o) σ x = 0 := by
          unfold dirDeriv
          rw [fderiv_of_notMem_tsupport ℝ hn]
          rfl
        simp [D, hσ0, hσ1]
      _ = 0 := hDpack.2
  have he (x : Space n) (hx : x ∈ Ω) :
      ρ x * (Z x * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) q x * dirDeriv (coordinateVector n j) q x) *
          deriv (deriv ψ) (q x) +
        (n : ℝ) * ((a o + b * c + d) - q x) * deriv ψ (q x) -
        (n : ℝ) * ((n : ℝ) + 1) * ψ (q x)) = F x - ((n : ℝ) + 2) * D x := by
    have hσeq : σ =ᶠ[nhds x] (fun y => ψ (q y)) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact Set.indicator_of_mem hy _
    have hηeq : η =ᶠ[nhds x] (fun y => Z y * ψ (q y)) :=
      hσeq.mono fun y hy => congrArg (Z y * ·) hy
    have hσderiv : dirDeriv (x - o) σ x = deriv ψ (q x) * dirDeriv (x - o) q x := by
      unfold dirDeriv
      rw [hσeq.fderiv_eq]
      exact dirDeriv_comp_scalar ((hq.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
        (hψ.differentiable (by simp) (q x)) (x - o)
    -- `F` uses the zero-extension, so transfer its Hessian by equality of germs.
    have hFexp' : F x =
      ρ x * (Z x * (∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n i) q x * dirDeriv (coordinateVector n j) q x) *
            deriv (deriv ψ) (q x) +
        n * Z x * b * deriv ψ (q x) + 2 * dirDeriv (x - o) q x * deriv ψ (q x) +
        n * ψ (q x)) + ((n : ℝ) + 2) * ψ (q x) * dirDeriv (x - o) ρ x := by
      dsimp only [F]
      rw [hessian_eq_of_eventuallyEq hηeq]
      exact weighted_trace_capTest hΩ hu hx (hpos x hx) o c a b d hψ
    rw [hFexp']
    dsimp only [D]
    rw [hσeq.eq_of_nhds, hσderiv]
    have hc := cap_affine_cancellation ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt
      (by simp)) o c a b d
    change Z x * b - dirDeriv (x - o) q x = (a o + b * c + d) - q x at hc
    linear_combination -ρ x * (n : ℝ) * deriv ψ (q x) * hc
  calc
    _ = ∫ x in Ω, F x - ((n : ℝ) + 2) * D x :=
      setIntegral_congr_fun hΩ.measurableSet he
    _ = (∫ x in Ω, F x) - ((n : ℝ) + 2) * ∫ x in Ω, D x := by
      rw [integral_sub hFint (hDpack.1.integrableOn.const_mul _), integral_const_mul]
    _ = 0 := by rw [hFzero, hDzero]; ring

end AffineBernstein

end

end OAI
