import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.DistanceSquare

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Matrix Function
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagonal_one_zero_perturbation (a : ι → ℝ) (i : ι)
    (hzero : a i = 0) (ha : ∀ j, j ≠ i → a j ≠ 0)
    (B : Matrix ι ι ℝ) (hB : B i i ≠ 0) :
    ∃ t : ℝ, (diagonal a + t • B).det ≠ 0 := by
  let d : ι → ℝ := Function.update a i 1
  have hd (j : ι) : d j ≠ 0 := by
    by_cases hj : j = i
    · subst j; simp [d]
    · simpa [d, hj] using ha j hj
  have hdet : (diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hd j)
  have hv : B i = ∑ j, (B i j / d j) • (diagonal d) j := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, diagonal_apply]
    rw [Finset.sum_eq_single k]
    · rw [ite_eq_left rfl, div_mul_cancel₀ _ (hd k)]
    · intro b _ hb; rw [ite_eq_right hb, mul_zero]
    · simp
  have hbase : ((diagonal a).updateRow i (B i)).det ≠ 0 := by
    have he : (diagonal a).updateRow i (B i) = (diagonal d).updateRow i (B i) := by
      ext j k
      by_cases hj : j = i
      · subst j; simp
      · simp only [Matrix.updateRow_apply, ite_eq_right hj, diagonal_apply]
        simp [d, hj]
    rw [he, hv, Matrix.det_updateRow_sum]
    simpa [d] using mul_ne_zero hB hdet
  have hc : Continuous (fun t : ℝ => ((diagonal a + t • B).updateRow i (B i)).det) := by
    apply Continuous.matrix_det
    apply continuous_pi; intro j
    apply continuous_pi; intro k
    by_cases hj : j = i
    · subst j; simpa using continuous_const (y := B i k)
    · simp only [Matrix.updateRow_apply, ite_eq_right hj]
      fun_prop
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ((diagonal a + t • B).updateRow i (B i)).det ≠ 0 :=
    hc.continuousAt.eventually_ne (by simpa using hbase)
  have hn' : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ((diagonal a + t • B).updateRow i (B i)).det ≠ 0 :=
    hn.filter_mono nhdsWithin_le_nhds
  have hz : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := eventually_mem_nhdsWithin
  obtain ⟨t,ht,ht0⟩ := (hn'.and hz).exists
  refine ⟨t, ?_⟩
  have hr : (diagonal a + t • B) i = t • B i := by
    ext j
    simp [diagonal_apply, hzero]
  have he : (diagonal a + t • B).det =
      t * ((diagonal a + t • B).updateRow i (B i)).det := by
    conv_lhs => rw [← Matrix.updateRow_eq_self (diagonal a + t • B) i, hr]
    exact Matrix.det_updateRow_smul _ _ _ _
  rw [he]
  exact mul_ne_zero ht0 ht

theorem symmetric_pencil_nondegenerate
    (L : Submodule ℝ (Matrix ι ι ℝ))
    (hL : ∀ A ∈ L, A.IsHermitian)
    (hsep : ∀ v : ι → ℝ, v ≠ 0 → ∃ B ∈ L, v ⬝ᵥ (B *ᵥ v) ≠ 0) :
    ∃ A ∈ L, A.det ≠ 0 := by
  let S : Set ℕ := {r | ∃ A ∈ L, A.rank = r}
  have hSf : S.Finite := (Set.finite_Iic (Fintype.card ι)).subset (by
    rintro r ⟨A,_,rfl⟩
    exact A.rank_le_card_width)
  obtain ⟨r,hr,hrmax⟩ := hSf.exists_maximal ⟨0, 0, L.zero_mem, by simp⟩
  obtain ⟨A,hAL,hAr⟩ := hr
  have hmax (B : Matrix ι ι ℝ) (hBL : B ∈ L) : B.rank ≤ A.rank := by
    by_contra hb
    have hle : r ≤ B.rank := by omega
    have := hrmax ⟨B,hBL,rfl⟩ hle
    omega
  have hA := hL A hAL
  by_cases hdet : A.det ≠ 0
  · exact ⟨A,hAL,hdet⟩
  have heig : ∃ i, hA.eigenvalues i = 0 := by
    by_contra! hh
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hh i)
  obtain ⟨i,hi⟩ := heig
  let U := hA.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star U)
  have hFA : F A = diagonal hA.eigenvalues := by
    simpa [F,U] using hA.conjStarAlgAut_star_eigenvectorUnitary
  let v : ι → ℝ := fun j => U j i
  have hv : v ≠ 0 := by
    intro hz
    have hh : hA.eigenvectorBasis i = 0 := by
      apply PiLp.ext; intro j
      exact congrFun hz j
    exact hA.eigenvectorBasis.toBasis.ne_zero i hh
  obtain ⟨B,hBL,hB⟩ := hsep v hv
  have hFB : F B i i ≠ 0 := by
    convert hB using 1
    simp only [F, Unitary.conjStarAlgAut_star_apply, Matrix.mul_apply,
      Matrix.star_apply, star_trivial, dotProduct, mulVec, v]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  let J := Option {j // hA.eigenvalues j ≠ 0}
  let e : J → ι := fun j => j.elim i Subtype.val
  have hei : Function.Injective e := by
    intro j k he
    cases j with
    | none => cases k with
      | none => rfl
      | some k =>
        have hk : i = k.val := he
        exact (k.property (hk ▸ hi)).elim
    | some j => cases k with
      | none =>
        have hj : j.val = i := he
        exact (j.property (hj ▸ hi)).elim
      | some k => exact congrArg some (Subtype.ext he)
  have hae (j : J) (hj : j ≠ none) : hA.eigenvalues (e j) ≠ 0 := by
    cases j with
    | none => exact (hj rfl).elim
    | some j => exact j.property
  obtain ⟨t,ht⟩ := diagonal_one_zero_perturbation
    (fun j : J => hA.eigenvalues (e j)) none hi hae
    ((F B).submatrix e e) hFB
  have hminor : (F (A + t • B)).submatrix e e =
      diagonal (fun j : J => hA.eigenvalues (e j)) + t • (F B).submatrix e e := by
    rw [map_add, map_smul, hFA, Matrix.submatrix_add, Matrix.submatrix_smul]
    change (diagonal hA.eigenvalues).submatrix e e + t • (F B).submatrix e e = _
    rw [Matrix.submatrix_diagonal _ _ hei]
    rfl
  have hrank (C : Matrix ι ι ℝ) : (F C).rank = C.rank := by
    simp only [F, Unitary.conjStarAlgAut_star_apply]
    simp [-isUnit_iff_ne_zero, ← Unitary.coe_star]
  have hbig : Fintype.card J ≤ (A + t • B).rank := by
    have hnt : ((F (A + t • B)).submatrix e e).det ≠ 0 := by rw [hminor]; exact ht
    rw [← hrank, ← Matrix.rank_of_det_ne_zero hnt]
    exact Matrix.rank_submatrix_le _ _ _
  have hsmall := hmax (A + t • B) (L.add_mem hAL (L.smul_mem t hBL))
  rw [hA.rank_eq_card_non_zero_eigs] at hsmall
  have hcard : Fintype.card J = Fintype.card {j // hA.eigenvalues j ≠ 0} + 1 :=
    Fintype.card_option
  omega

end


open LinearMap
open scoped Matrix

theorem symmetric_forms_nondegenerate
    {P W : Type*} [AddCommGroup P] [Module ℝ P]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : P →ₗ[ℝ] LinearMap.BilinForm ℝ W)
    (hB : ∀ p x y, B p x y = B p y x)
    (hsep : ∀ w : W, w ≠ 0 → ∃ p, B p w w ≠ 0) :
    ∃ p, (B p).Nondegenerate := by
  classical
  let b := Module.finBasis ℝ W
  let L := ((LinearMap.BilinForm.toMatrix b).toLinearMap.comp B).range
  have hs : ∀ A ∈ L, A.IsHermitian := by
    rintro A ⟨p,rfl⟩
    rw [Matrix.isHermitian_iff_isSymm]
    exact (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm b).mpr ⟨hB p⟩
  have hh : ∀ v : Fin (Module.finrank ℝ W) → ℝ, v ≠ 0 →
      ∃ A ∈ L, v ⬝ᵥ (A *ᵥ v) ≠ 0 := by
    intro v hv
    have hw : b.equivFun.symm v ≠ 0 := by
      intro hz
      apply hv
      apply b.equivFun.symm.injective
      exact hz.trans (map_zero b.equivFun.symm).symm
    obtain ⟨p,hp⟩ := hsep _ hw
    refine ⟨(B p).toMatrix b,⟨p,rfl⟩,?_⟩
    simpa only [LinearMap.BilinForm.dotProduct_toMatrix_mulVec] using hp
  obtain ⟨A,⟨p,rfl⟩,hA⟩ := symmetric_pencil_nondegenerate L hs hh
  exact ⟨p,(LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr hA⟩

end YauCounterexamples
end

end OAI
