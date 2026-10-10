import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section MatrixConcavity
open scoped MatrixOrder

/-- Weighted arithmetic-geometric mean for the eigenvalues, with the unused
weight placed at 1. This is the determinant-power supporting inequality at I. -/
theorem det_rpow_le_one_add_trace {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ) (hnδ : (n : ℝ) * δ ≤ 1) :
    H.det ^ δ ≤ 1 + δ * (H.trace - n) := by
  let w : Option (Fin n) → ℝ := fun i => i.elim (1 - (n : ℝ) * δ) (fun _ => δ)
  let z : Option (Fin n) → ℝ := fun i => i.elim 1 hH.isHermitian.eigenvalues
  have hw : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i hi
    cases i with
    | none => exact sub_nonneg.mpr hnδ
    | some i => exact hδ
  have hsum : (∑ i, w i) = 1 := by
    simp [w, Fintype.sum_option]
  have hz : ∀ i ∈ Finset.univ, 0 ≤ z i := by
    intro i hi
    cases i with
    | none => exact zero_le_one
    | some i => exact hH.eigenvalues_nonneg i
  have hg := Real.geom_mean_le_arith_mean_weighted Finset.univ w z hw hsum hz
  simp only [Fintype.prod_option, Fintype.sum_option, w, z, Option.elim_none,
    Option.elim_some, Real.one_rpow, one_mul, mul_one] at hg
  have hd : H.det = ∏ i, hH.isHermitian.eigenvalues i := by
    simpa using hH.isHermitian.det_eq_prod_eigenvalues
  have ht : H.trace = ∑ i, hH.isHermitian.eigenvalues i := by
    simpa using hH.isHermitian.trace_eq_sum_eigenvalues
  rw [Real.finsetProd_rpow _ _ (fun i hi => hH.eigenvalues_nonneg i),
    ← hd, ← Finset.mul_sum, ← ht] at hg
  linarith

/-- Congruence by the inverse positive square root converts the determinant
ratio and the mixed trace to the same positive semidefinite matrix. -/
theorem exists_normalized_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    ∃ C : Matrix (Fin n) (Fin n) ℝ, C.PosSemidef ∧
      C.det = B.det / A.det ∧ C.trace = (A⁻¹ * B).trace := by
  let S := CFC.sqrt A⁻¹
  have hS : S.conjTranspose = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A⁻¹)).isHermitian.eq
  have hSsq : S * S = A⁻¹ := by
    simpa only [S, pow_two] using CFC.sq_sqrt A⁻¹ hA.inv.posSemidef.nonneg
  let C := S * B * S.conjTranspose
  refine ⟨C, hB.mul_mul_conjTranspose_same S, ?_, ?_⟩
  · calc
      C.det = (S * S).det * B.det := by
        simp only [C, hS, Matrix.det_mul]
        ring
      _ = B.det / A.det := by
        rw [hSsq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
        ring
  · dsimp only [C]
    rw [hS, Matrix.trace_mul_cycle, hSsq]

/-- Concavity in its precise tangent form, for all exponents in [0,1/n]. -/
theorem det_rpow_tangent_inequality {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) {δ : ℝ} (hδ : 0 ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1) :
    B.det ^ δ ≤ A.det ^ δ + δ * A.det ^ δ * (A⁻¹ * (B - A)).trace := by
  obtain ⟨C, hC, hCd, hCt⟩ := exists_normalized_posSemidef hA hB
  have hscalar := det_rpow_le_one_add_trace hC hδ hnδ
  rw [hCd, hCt] at hscalar
  have hpos : 0 < A.det ^ δ := Real.rpow_pos_of_pos hA.det_pos δ
  have htrace : (A⁻¹ * (B - A)).trace = (A⁻¹ * B).trace - n := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos))]
    simp
  calc
    B.det ^ δ = A.det ^ δ * (B.det / A.det) ^ δ := by
      rw [Real.div_rpow hB.det_nonneg hA.det_pos.le]
      field_simp
    _ ≤ A.det ^ δ * (1 + δ * ((A⁻¹ * B).trace - n)) :=
      mul_le_mul_of_nonneg_left hscalar hpos.le
    _ = _ := by rw [htrace]; ring

end MatrixConcavity

/-- On an open set the Hessian is additive; no extension outside that set is used. -/
theorem hessian_add_on {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => u y + v y) x = hessian u x + hessian v x := by
  ext i j
  have he : (fun y => fderiv ℝ (fun z => u z + v z) y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ u y (coordinateVector n j) + fderiv ℝ v y (coordinateVector n j)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [fderiv_fun_add ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hv.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))]
    rfl
  change fderiv ℝ (fun y => fderiv ℝ (fun z => u z + v z) y (coordinateVector n j)) x (coordinateVector n i) =
    fderiv ℝ (fun y => fderiv ℝ u y (coordinateVector n j)) x (coordinateVector n i) +
    fderiv ℝ (fun y => fderiv ℝ v y (coordinateVector n j)) x (coordinateVector n i)
  rw [he.fderiv_eq]
  change fderiv ℝ (fun y => dirDeriv (coordinateVector n j) u y + dirDeriv (coordinateVector n j) v y) x (coordinateVector n i) =
    fderiv ℝ (dirDeriv (coordinateVector n j) u) x (coordinateVector n i) +
    fderiv ℝ (dirDeriv (coordinateVector n j) v) x (coordinateVector n i)
  rw [fderiv_fun_add
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) (coordinateVector n j)).differentiableAt (by simp))
    ((contDiffAt_dirDeriv (hv.contDiffAt (hΩ.mem_nhds hx)) (coordinateVector n j)).differentiableAt (by simp))]
  rfl

theorem hessian_isSymm {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : (hessian u x).IsSymm := by
  ext i j
  exact dirDeriv_comm hu (coordinateVector n j) (coordinateVector n i)

theorem matrix_trace_pair {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsSymm) : (A * B).trace = ∑ i, ∑ j, A i j * B i j := by
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ j, A i j * B j i) = ∑ j, A i j * B i j
  apply Finset.sum_congr rfl
  intro j hj
  rw [hB.apply j i]

/-- The actual determinant density obeys its supporting-hyperplane inequality. -/
theorem affineArea_tangent_inequality {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u η : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    {x : Space n} (hx : x ∈ Ω) (hpos : (hessian u x).PosDef)
    (hpert : (hessian (fun y => u y + η y) x).PosSemidef) :
    affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x ≤
      (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hnd : (n : ℝ) * (1 / ((n : ℝ) + 2)) ≤ 1 := by
    rw [mul_one_div, div_le_one hn]
    linarith
  have hp := det_rpow_tangent_inequality hpos hpert (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2)) hnd
  have he : hessian (fun y => u y + η y) x - hessian u x = hessian η x := by
    rw [hessian_add_on hΩ hu hη hx]
    abel
  rw [he, matrix_trace_pair _ _ (hessian_isSymm (hη.contDiffAt (hΩ.mem_nhds hx)))] at hp
  change _ - _ ≤ _ * (_ * _)
  unfold affineAreaDensity
  simp only [Real.rpow_eq_pow]
  nlinarith [hp]

/-- Density differences for a compactly supported perturbation really are
integrable, although each area on an unbounded domain could be infinite. -/
theorem integrableOn_affineArea_difference {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω)
    (hpert : ∀ y ∈ Ω, (hessian (fun z => u z + η z) y).PosDef) :
    IntegrableOn (fun x => affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x) Ω := by
  apply Integrable.integrableOn
  apply integrable_of_support_subset_compact hηc.isCompact
  · intro x hx
    by_contra hn
    have he : (fun y => u y + η y) =ᶠ[nhds x] u := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [hy, add_zero]
    exact hx (by
      change affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x = 0
      unfold affineAreaDensity
      rw [hessian_eq_of_eventuallyEq he]
      exact sub_self _)
  · intro x hx
    have hux := hu.contDiffAt (hΩ.mem_nhds (hηΩ hx))
    exact ((contDiffAt_affineAreaDensity (hux.add hη.contDiffAt) (hpert x (hηΩ hx))).sub
      (contDiffAt_affineAreaDensity hux (hpos x (hηΩ hx)))).continuousAt.continuousWithinAt

/-- Local maximization of graph affine area, deduced from the PDE rather than
assumed as stability. -/
theorem affineMaximal_local_area_maximization {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    (η : Space n → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω)
    (hpert : ∀ y ∈ Ω, (hessian (fun z => u z + η z) y).PosDef) :
    (∫ x in Ω, affineAreaDensity (fun y => u y + η y) x - affineAreaDensity u x) ≤ 0 := by
  have hi := integrableOn_affineArea_difference hΩ hu hpos η hη hηc hηΩ hpert
  have hv := integrableOn_area_variation hΩ hu hpos η hη hηc hηΩ
  calc
    _ ≤ ∫ x in Ω, (1 / ((n : ℝ) + 2)) * (affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j)) := by
      apply integral_mono_ae hi (hv.const_mul _)
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact affineArea_tangent_inequality hΩ hu hη.contDiffOn hx (hpos x hx) (hpert x hx).posSemidef
    _ = 0 := by
      rw [integral_const_mul, affineMaximal_area_stationarity hΩ hu hpos hmax η hη hηc hηΩ, mul_zero]

/-- The affine pullback uses the continuous map associated with the actual
matrix, so its determinant and nonsingularity have their usual meanings. -/
def affineBaseMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (y : Space n) : Space n :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B y + d

@[simp] theorem euclideanCLM_coordinateVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j) i = B i j := by
  change Matrix.mulVec B (Pi.single j 1) i = B i j
  simp

/-- First derivative of composition with an affine base change. -/
theorem dirDeriv_comp_affine {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n)
    {u : Space n → ℝ} {x : Space n} (hu : DifferentiableAt ℝ u (affineBaseMap B d x))
    (v : Space n) :
    dirDeriv v (fun y => u (affineBaseMap B d y)) x =
      dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B v) u (affineBaseMap B d x) := by
  have ht : HasFDerivAt (affineBaseMap B d) (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B) x := by
    exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).hasFDerivAt.add_const d
  change fderiv ℝ (u ∘ affineBaseMap B d) x v = _
  rw [(hu.hasFDerivAt.comp x ht).fderiv]
  rfl

/-- The Hessian chain rule, retaining the exact order Bᵀ H B. -/
theorem hessian_comp_affine {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) {x : Space n}
    (hx : affineBaseMap B d x ∈ Ω) :
    hessian (fun y => u (affineBaseMap B d y)) x =
      B.transpose * hessian u (affineBaseMap B d x) * B := by
  have hT : Continuous (affineBaseMap B d) := by unfold affineBaseMap; fun_prop
  have hΩ' : IsOpen (affineBaseMap B d ⁻¹' Ω) := hΩ.preimage hT
  ext i j
  have he : dirDeriv (coordinateVector n j) (fun y => u (affineBaseMap B d y)) =ᶠ[nhds x]
      (fun y => dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j)) u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact dirDeriv_comp_affine B d ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) _
  change fderiv ℝ (dirDeriv (coordinateVector n j) (fun y => u (affineBaseMap B d y))) x (coordinateVector n i) =
    (B.transpose * hessian u (affineBaseMap B d x) * B) i j
  rw [he.fderiv_eq]
  change dirDeriv (coordinateVector n i) (fun y =>
    dirDeriv (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j)) u (affineBaseMap B d y)) x = _
  rw [dirDeriv_comp_affine B d
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp))]
  rw [dirDeriv_eq_second (hu.contDiffAt (hΩ.mem_nhds hx))]
  rw [← sum_coordinateVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n i)),
      ← sum_coordinateVector (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B (coordinateVector n j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, euclideanCLM_coordinateVector, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hd : fderiv ℝ (fderiv ℝ u) (affineBaseMap B d x) (coordinateVector n l) (coordinateVector n k) =
      hessian u (affineBaseMap B d x) l k :=
    (dirDeriv_eq_second (hu.contDiffAt (hΩ.mem_nhds hx)) _ _).symm
  rw [hd]
  ring

/-- Multiplying heights by a scalar multiplies the actual Hessian by it. -/
theorem hessian_const_mul {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (c : ℝ) {x : Space n} (hx : x ∈ Ω) :
    hessian (fun y => c * u y) x = c • hessian u x := by
  ext i j
  have he : (fun y => fderiv ℝ (fun z => c * u z) y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => c * dirDeriv (coordinateVector n j) u y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [fderiv_const_mul ((hu.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) c]
    rfl
  change fderiv ℝ _ x (coordinateVector n i) = c * _
  rw [he.fderiv_eq, fderiv_const_mul
    ((contDiffAt_dirDeriv (hu.contDiffAt (hΩ.mem_nhds hx)) _).differentiableAt (by simp)) c]
  rfl

/-- Nonsingular congruence and positive scalar multiplication preserve strict
ellipticity. The condition on B is exactly invertibility, not orthogonality. -/
theorem posDef_affine_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c) :
    (c • (B.transpose * H * B)).PosDef := by
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hB)
  have hBt : B.conjTranspose = B.transpose := by ext i j; simp
  simpa only [hBt] using
    (hH.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hBu)).smul hc

/-- Exact determinant normalization used for rescaled sections. -/
theorem det_affine_congruence {n : ℕ} (H B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (c • (B.transpose * H * B)).det = (c ^ n * B.det ^ 2) * H.det := by
  simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- The trace contraction is invariant under simultaneous congruence, with the
exact scalar ratio. This is the algebra behind covariance of the affine PDE. -/
theorem trace_inverse_congruence {n : ℕ} {H B : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c)
    (K : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ((c • (B.transpose * H * B))⁻¹ * (t • (B.transpose * K * B))).trace =
    (c⁻¹ * t) * (H⁻¹ * K).trace := by
  let : Invertible c := invertibleOfNonzero (ne_of_gt hc)
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBt : IsUnit B.transpose.det := by simpa using hBu
  have hPu : IsUnit (B.transpose * H * B).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hB (ne_of_gt hH.det_pos)) hB
  rw [Matrix.inv_smul _ c hPu, invOf_eq_inv, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  suffices hs : (((B.transpose * H * B)⁻¹) * (B.transpose * K * B)).trace =
      (H⁻¹ * K).trace by rw [hs]; ring
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have he : (B⁻¹ * (H⁻¹ * B.transpose⁻¹)) * (B.transpose * K * B) =
      B⁻¹ * (H⁻¹ * K) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B.transpose⁻¹ B.transpose, Matrix.nonsing_inv_mul _ hBt, one_mul]
  rw [he, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hBu, one_mul]

/-- The classical PDE is equivalent to the inverse-Hessian trace formulation
wherever its coefficients are the actual positive-definite Hessian. -/
theorem affineMaximalOn_iff_trace {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) :
    AffineMaximalOn Ω u ↔ ∀ x ∈ Ω,
      ((hessian u x)⁻¹ * hessian (affineWeight u) x).trace = 0 := by
  apply forall₂_congr
  intro x hx
  have hw := hessian_isSymm (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hx)) (hpos x hx))
  rw [matrix_trace_pair _ _ hw]
  change (∑ i, ∑ j, (hessian u x).det * (hessian u x)⁻¹ i j * hessian (affineWeight u) x i j) = 0 ↔ _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  exact mul_eq_zero_iff_left (ne_of_gt (hpos x hx).det_pos)

/-- Change of base variables, positive vertical scaling, and arbitrary affine
height correction. This includes the normalization of sections in rigidity. -/
def affineGraphPullback {n : ℕ} (u : Space n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) : Space n → ℝ :=
  graphAffineFunction (fun y => u (affineBaseMap B d y)) a c e

theorem contDiff_affineBaseMap {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) :
    ContDiff ℝ ∞ (affineBaseMap B d) := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B).contDiff.add contDiff_const

theorem contDiffOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ) :
    ContDiffOn ℝ ∞ (affineGraphPullback u B d a c e) (affineBaseMap B d ⁻¹' Ω) := by
  have hut := hu.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  exact (a.contDiff.contDiffOn.add (contDiffOn_const.mul hut)).add contDiffOn_const

theorem hessian_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (B : Matrix (Fin n) (Fin n) ℝ) (d : Space n) (a : Space n →L[ℝ] ℝ) (c e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    hessian (affineGraphPullback u B d a c e) x =
      c • (B.transpose * hessian u (affineBaseMap B d x) * B) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hut := hu.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hh : hessian (affineGraphPullback u B d a c e) x =
      c • hessian (fun y => u (affineBaseMap B d y)) x := by
    ext i j
    exact hessian_graphAffineFunction hΩ' hut hx a c e i j
  rw [hh, hessian_comp_affine hΩ hu B d hx]

theorem posDef_hessian_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    (hessian (affineGraphPullback u B d a c e) x).PosDef := by
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx]
  exact posDef_affine_congruence (hpos _ hx) hB hc

/-- The actual determinant weight transforms by its exact positive constant. -/
theorem affineWeight_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ)
    {x : Space n} (hx : affineBaseMap B d x ∈ Ω) :
    affineWeight (affineGraphPullback u B d a c e) x =
      Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2))) *
        affineWeight u (affineBaseMap B d x) := by
  unfold affineWeight
  rw [hessian_affineGraphPullback hΩ hu B d a c e hx, det_affine_congruence]
  exact Real.mul_rpow (mul_nonneg (pow_nonneg hc.le _) (sq_pos_of_ne_zero hB).le)
    (hpos _ hx).det_pos.le

/-- Hessians are local, including their inner derivative. -/
theorem hessian_congr_nhds {n : ℕ} {u v : Space n → ℝ} {x : Space n}
    (he : u =ᶠ[nhds x] v) : hessian u x = hessian v x := by
  ext i j
  have hd : (fun y => fderiv ℝ u y (coordinateVector n j)) =ᶠ[nhds x]
      (fun y => fderiv ℝ v y (coordinateVector n j)) :=
    he.fderiv.mono (fun _ hy => congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n j)) hy)
  exact congrArg (fun f : Space n →L[ℝ] ℝ => f (coordinateVector n i)) hd.fderiv_eq

/-- Exact, classical affine-maximal PDE covariance for section normalization.
No transformed PDE is assumed: it follows from the original one by the actual
Hessian and determinant chain rules. -/
theorem affineMaximalOn_affineGraphPullback {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hpos : ∀ y ∈ Ω, (hessian u y).PosDef) (hmax : AffineMaximalOn Ω u)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.det ≠ 0) (d : Space n)
    (a : Space n →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (e : ℝ) :
    AffineMaximalOn (affineBaseMap B d ⁻¹' Ω) (affineGraphPullback u B d a c e) := by
  have hΩ' := hΩ.preimage (contDiff_affineBaseMap B d).continuous
  have hv := contDiffOn_affineGraphPullback hu B d a c e
  have hpv : ∀ x ∈ affineBaseMap B d ⁻¹' Ω,
      (hessian (affineGraphPullback u B d a c e) x).PosDef :=
    fun _ hx => posDef_hessian_affineGraphPullback hΩ hu hpos hB d a hc e hx
  apply (affineMaximalOn_iff_trace hΩ' hv hpv).mpr
  intro x hx
  let t := Real.rpow (c ^ n * B.det ^ 2) (-(((n : ℝ) + 1) / ((n : ℝ) + 2)))
  have hw : ContDiffOn ℝ ∞ (affineWeight u) Ω := by
    intro y hy
    exact (contDiffAt_affineWeight (hu.contDiffAt (hΩ.mem_nhds hy)) (hpos y hy)).contDiffWithinAt
  have hwt : ContDiffOn ℝ ∞ (fun y => affineWeight u (affineBaseMap B d y))
      (affineBaseMap B d ⁻¹' Ω) :=
    hw.comp (contDiff_affineBaseMap B d).contDiffOn (fun _ hx => hx)
  have hew : affineWeight (affineGraphPullback u B d a c e) =ᶠ[nhds x]
      (fun y => t * affineWeight u (affineBaseMap B d y)) := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact affineWeight_affineGraphPullback hΩ hu hpos hB d a hc e hy
  rw [hessian_congr_nhds hew, hessian_const_mul hΩ' hwt t hx,
    hessian_comp_affine hΩ hw B d hx, hessian_affineGraphPullback hΩ hu B d a c e hx,
    trace_inverse_congruence (hpos _ hx) hB hc,
    (affineMaximalOn_iff_trace hΩ hu hpos).mp hmax _ hx, mul_zero]

end AffineBernstein

end

end OAI
