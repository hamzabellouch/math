import OAI.Geometry.ProjectionVolume.ProjectionJacobian

namespace OAI

universe uι

open Set
open scoped RealInnerProductSpace

namespace Paper092

noncomputable def augmentedTangentMatrix {d : ℕ} {ι : Type uι} [Fintype ι]
    (v : Euclidean d) (b : OrthonormalBasis ι ℝ (normalHyperplane v))
    (B : OrthonormalBasis (ι ⊕ Fin 1) ℝ (Euclidean d)) (u : Euclidean d) :
    Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℝ :=
  fun i j => ⟪B i, Sum.elim (fun k => (b k : Euclidean d)) (fun _ => u) j⟫

theorem abs_det_augmentedTangentMatrix {d : ℕ} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (v : Euclidean d) (hv : ‖v‖ = 1) (b : OrthonormalBasis ι ℝ (normalHyperplane v))
    (B : OrthonormalBasis (ι ⊕ Fin 1) ℝ (Euclidean d)) (u : Euclidean d) :
    |(augmentedTangentMatrix v b B u).det| = |⟪u, v⟫| := by
  let w : ι ⊕ Fin 1 → Euclidean d := Sum.elim (fun k => (b k : Euclidean d)) (fun _ => u)
  let a : ι → ℝ := fun i => ⟪u, (b i : Euclidean d)⟫
  let M := augmentedTangentMatrix v b B u
  have hgram : Matrix.gram ℝ w = Matrix.fromBlocks
      (1 : Matrix ι ι ℝ) (Matrix.of fun i (_ : Fin 1) => a i)
      (Matrix.of fun (_ : Fin 1) j => a j)
      (Matrix.of fun (_ _ : Fin 1) => ‖u‖ ^ 2) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · exact b.inner_eq_ite i j
    · change ⟪(b i : Euclidean d), u⟫ = ⟪u, (b i : Euclidean d)⟫
      exact real_inner_comm _ _
    · rfl
    · exact real_inner_self_eq_norm_sq u
  have hsum : (∑ i, a i ^ 2) = ‖u‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
    have h := b.sum_sq_inner_left ((normalHyperplane v).orthogonalProjectionOnto u)
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at h
    change (∑ i, a i ^ 2) = ‖(normalHyperplane v).orthogonalProjectionOnto u‖ ^ 2 at h
    rw [h]
    change ‖(normalHyperplane v).starProjection u‖ ^ 2 = _
    rw [normal_starProjection_unit v u hv, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [real_inner_comm v u]
    ring
  have hgdet : (Matrix.gram ℝ w).det = ⟪u, v⟫ ^ 2 := by
    rw [hgram, Matrix.det_fromBlocks_one₁₁, Matrix.det_unique]
    change ‖u‖ ^ 2 - (∑ i, a i * a i) = ⟪u, v⟫ ^ 2
    simp_rw [← pow_two]
    rw [hsum]
    ring
  have hfactor : M.transpose * M = Matrix.gram ℝ w := by
    ext i j
    change (∑ k, ⟪B k, w i⟫ * ⟪B k, w j⟫) = ⟪w i, w j⟫
    calc
      (∑ k, ⟪B k, w i⟫ * ⟪B k, w j⟫) =
          ∑ k, ⟪w i, B k⟫ * ⟪B k, w j⟫ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [real_inner_comm (B k) (w i)]
      _ = ⟪w i, w j⟫ := B.sum_inner_mul_inner _ _
  have hsquare : M.det ^ 2 = ⟪u, v⟫ ^ 2 := by
    calc
      M.det ^ 2 = (M.transpose * M).det := by
        rw [Matrix.det_mul, Matrix.det_transpose, pow_two]
      _ = (Matrix.gram ℝ w).det := congrArg Matrix.det hfactor
      _ = ⟪u, v⟫ ^ 2 := hgdet
  change |M.det| = _
  nlinarith [sq_abs M.det, sq_abs ⟪u, v⟫, abs_nonneg M.det, abs_nonneg ⟪u, v⟫]

noncomputable def tangentColumns {n : ℕ} (v : Euclidean (n + 1))
    (b : OrthonormalBasis (Fin n) ℝ (normalHyperplane v)) (u : Euclidean (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => (Fin.append (fun k => (b k : Euclidean (n + 1))) (fun _ : Fin 1 => u) j) i

theorem abs_det_tangentColumns {n : ℕ} (v : Euclidean (n + 1)) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin n) ℝ (normalHyperplane v)) (u : Euclidean (n + 1)) :
    |(tangentColumns v b u).det| = |⟪u, v⟫| := by
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  let B : OrthonormalBasis (Fin n ⊕ Fin 1) ℝ (Euclidean (n + 1)) :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).reindex e.symm
  have hB (i : Fin n ⊕ Fin 1) : B i = EuclideanSpace.single (e i) 1 := by
    rw [OrthonormalBasis.reindex_apply]
    exact EuclideanSpace.basisFun_apply (Fin (n + 1)) ℝ (e i)
  have hm : augmentedTangentMatrix v b B u = (tangentColumns v b u).submatrix e e := by
    ext i j
    change ⟪B i, Sum.elim (fun k => (b k : Euclidean (n + 1))) (fun _ => u) j⟫ =
      (Fin.append (fun k => (b k : Euclidean (n + 1))) (fun _ : Fin 1 => u) (e j)) (e i)
    rw [hB]
    rcases j with j | j
    · simp [e, EuclideanSpace.inner_single_left]
    · simp [e, EuclideanSpace.inner_single_left]
  have h := abs_det_augmentedTangentMatrix v hv b B u
  rw [hm, Matrix.det_submatrix_equiv_self] at h
  exact h

theorem hyperplaneProjection_normDet_eq_abs_augmented_det {n : ℕ}
    (u v : Euclidean (n + 1)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (b : OrthonormalBasis (Fin n) ℝ (normalHyperplane v)) :
    (hyperplaneProjection u v).normDet = |(tangentColumns v b u).det| := by
  rw [hyperplaneProjection_normDet u v hu hv, abs_det_tangentColumns v hv b u]

end Paper092

end OAI
