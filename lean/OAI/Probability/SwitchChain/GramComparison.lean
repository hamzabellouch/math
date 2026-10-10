import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem gram_comparison_of_range
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (hinv : ∀ y : E, y ∈ LinearMap.range B → G y ∈ LinearMap.range B)
    (hcomp : ∀ c : F, ‖LinearMap.adjoint B (B c)‖ ^ 2 ≤ ⟪B c, G (B c)⟫)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  let M := LinearMap.range B
  let p := M.starProjection x
  let q := x - p
  have hp : p ∈ M := M.starProjection_apply_mem x
  have hq : q ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
  have hx : x = p + q := by dsimp only [q]; abel
  have hBq : LinearMap.adjoint B q = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [LinearMap.adjoint_inner_left]
    rw [real_inner_comm]
    exact hq (B (LinearMap.adjoint B q)) (LinearMap.mem_range_self _ _)
  have hcross : ⟪p, G q⟫ = 0 := by
    rw [← hG p q]
    exact hq (G p) (hinv p hp)
  have hcross' : ⟪q, G p⟫ = 0 := by
    rw [real_inner_comm]
    exact hq (G p) (hinv p hp)
  have hnorm : ‖LinearMap.adjoint B x‖ ^ 2 = ‖LinearMap.adjoint B p‖ ^ 2 := by
    rw [hx, map_add, hBq, add_zero]
  have hform : ⟪x, G x⟫ = ⟪p, G p⟫ + ⟪q, G q⟫ := by
    rw [hx, map_add, inner_add_left, inner_add_right, inner_add_right,
      hcross, hcross']
    ring
  obtain ⟨c, hc⟩ := hp
  have hccomp := hcomp c
  rw [hc] at hccomp
  rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hnorm, hform]
  exact hccomp.trans (le_add_of_nonneg_right (hpos q))

omit [FiniteDimensional ℝ F] in

theorem inner_basis_apply_of_diagonal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (A : F →ₗ[ℝ] F) (μ : ι → ℝ)
    (hdiag : ∀ i, A (b i) = μ i • b i) (c : F) (i : ι) :
    ⟪b i, A c⟫ = μ i * ⟪b i, c⟫ := by
  have hsum : A c = ∑ j, (b.repr c j * μ j) • b j := by
    calc
      A c = A (∑ j, b.repr c j • b j) := congrArg A (b.sum_repr c).symm
      _ = _ := by simp only [map_sum, map_smul, hdiag, smul_smul]
  rw [hsum, b.orthonormal.inner_right_fintype, b.repr_apply_apply]
  ring

theorem gram_comparison_of_eigenbasis {ι : Type*} [Fintype ι]
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (b : OrthonormalBasis ι ℝ F) (μ lam : ι → ℝ)
    (hgram : ∀ i, LinearMap.adjoint B (B (b i)) = μ i • b i)
    (himage : ∀ i, G (B (b i)) = lam i • B (b i))
    (hbound : ∀ i, μ i ≤ lam i) (x : E) :
    ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  classical
  have hμpos (i : ι) : 0 ≤ μ i := by
    have h := B.adjoint_inner_right (b i) (B (b i))
    have hunit : ⟪b i, b i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i]
      norm_num
    rw [hgram, inner_smul_right, hunit, mul_one, real_inner_self_eq_norm_sq] at h
    rw [h]
    positivity
  apply gram_comparison_of_range B G hG hpos
  · rintro y ⟨c, rfl⟩
    rw [← b.sum_repr c, map_sum, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul, map_smul, himage]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (LinearMap.mem_range_self B (b i)))
  · intro c
    let K := (LinearMap.adjoint B).comp B
    let L := (LinearMap.adjoint B).comp (G.comp B)
    have hK (i : ι) : K (b i) = μ i • b i := hgram i
    have hL (i : ι) : L (b i) = (lam i * μ i) • b i := by
      simp only [L, LinearMap.comp_apply, himage, map_smul, hgram, smul_smul]
    have hKcoord (i : ι) : ⟪b i, LinearMap.adjoint B (B c)⟫ =
        μ i * ⟪b i, c⟫ := inner_basis_apply_of_diagonal b K μ hK c i
    have hLcoord (i : ι) : ⟪b i, LinearMap.adjoint B (G (B c))⟫ =
        (lam i * μ i) * ⟪b i, c⟫ :=
      inner_basis_apply_of_diagonal b L (fun i => lam i * μ i) hL c i
    rw [← b.sum_sq_inner_right, ← B.adjoint_inner_right,
      ← b.sum_inner_mul_inner c (LinearMap.adjoint B (G (B c)))]
    apply Finset.sum_le_sum
    intro i hi
    rw [hKcoord, hLcoord]
    have hcomm : ⟪c, b i⟫ = ⟪b i, c⟫ := real_inner_comm _ _
    rw [hcomm]
    have hh := mul_le_mul_of_nonneg_right (hbound i) (hμpos i)
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ⟪b i, c⟫)
    nlinarith

theorem gram_comparison_of_two_blocks_without_signs
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hdecomp : ∀ c : F, ∃ u v : F,
      B c = B u + B v ∧ ⟪u, v⟫ = 0 ∧
      LinearMap.adjoint B (B u) = μ₁ • u ∧
      LinearMap.adjoint B (B v) = μ₂ • v ∧
      G (B u) = lam₁ • B u ∧ G (B v) = lam₂ • B v)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  apply gram_comparison_of_range B G hG hpos
  · rintro y ⟨c, rfl⟩
    obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
    rw [hc, map_add, hGu, hGv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (LinearMap.mem_range_self B u))
      (Submodule.smul_mem _ _ (LinearMap.mem_range_self B v))
  · intro c
    obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
    have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
    have hBu : ⟪B u, B u⟫ = μ₁ * ‖u‖ ^ 2 := by
      rw [← B.adjoint_inner_right, hKu, inner_smul_right, real_inner_self_eq_norm_sq]
    have hBv : ⟪B v, B v⟫ = μ₂ * ‖v‖ ^ 2 := by
      rw [← B.adjoint_inner_right, hKv, inner_smul_right, real_inner_self_eq_norm_sq]
    have hBuv : ⟪B u, B v⟫ = 0 := by
      rw [← B.adjoint_inner_right, hKv, inner_smul_right, huv, mul_zero]
    have hBvu : ⟪B v, B u⟫ = 0 := by rw [real_inner_comm]; exact hBuv
    rw [hc, map_add, hKu, hKv, ← real_inner_self_eq_norm_sq,
      map_add, hGu, hGv]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, huv, hvu, hBuv, hBvu, hBu, hBv,
      real_inner_self_eq_norm_sq, mul_zero, add_zero, zero_add]
    have hposu : 0 ≤ μ₁ * ‖u‖ ^ 2 := by
      rw [← hBu]
      rw [real_inner_self_eq_norm_sq]
      positivity
    have hposv : 0 ≤ μ₂ * ‖v‖ ^ 2 := by
      rw [← hBv]
      rw [real_inner_self_eq_norm_sq]
      positivity
    have h₁ := mul_le_mul_of_nonneg_right hbound₁ hposu
    have h₂ := mul_le_mul_of_nonneg_right hbound₂ hposv
    nlinarith

theorem gram_comparison_of_two_blocks
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ)
    (_hμ₁ : 0 ≤ μ₁) (_hμ₂ : 0 ≤ μ₂)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hdecomp : ∀ c : F, ∃ u v : F,
      B c = B u + B v ∧ ⟪u, v⟫ = 0 ∧
      LinearMap.adjoint B (B u) = μ₁ • u ∧
      LinearMap.adjoint B (B v) = μ₂ • v ∧
      G (B u) = lam₁ • B u ∧ G (B v) = lam₂ • B v)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ :=
  gram_comparison_of_two_blocks_without_signs B G hG hpos μ₁ μ₂ lam₁ lam₂
    hbound₁ hbound₂ hdecomp x

end Problem315.Analytic

end

end OAI
