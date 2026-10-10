import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Complex.Basic

namespace OAI

noncomputable section

namespace InvariantRotation.DiagonalAdjoint

open scoped ComplexConjugate

variable {ι : Type*}
abbrev Hilbert (ι : Type*) := lp (fun _ : ι => ℂ) 2

theorem isFormalAdjoint_diagonal
    (H G : Hilbert ι →ₗ.[ℂ] Hilbert ι) (h : ι → ℂ)
    (hH : ∀ x : H.domain, ∀ i, H x i = h i * x.val i)
    (hG : ∀ y : G.domain, ∀ i, G y i = conj (h i) * y.val i) :
    H.IsFormalAdjoint G := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  rw [hH, hG]
  simp only [RCLike.inner_apply, map_mul]
  ring

variable [DecidableEq ι]

theorem adjoint_apply_coordinate
    (H : Hilbert ι →ₗ.[ℂ] Hilbert ι) (h : ι → ℂ)
    (hdense : Dense (H.domain : Set (Hilbert ι)))
    (hsingle : ∀ i, lp.single 2 i (1 : ℂ) ∈ H.domain)
    (hH : ∀ x : H.domain, ∀ i, H x i = h i * x.val i)
    (y : H.adjoint.domain) (i : ι) :
    H.adjoint y i = conj (h i) * y.val i := by
  classical
  have hsingleMap : H ⟨lp.single 2 i (1 : ℂ), hsingle i⟩ =
      h i • lp.single 2 i (1 : ℂ) := by
    ext j
    rw [hH]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hji : j = i
    · subst j; rfl
    · simp [lp.single_apply, hji]
  have heq := (LinearPMap.adjoint_isFormalAdjoint hdense).symm
    ⟨lp.single 2 i (1 : ℂ), hsingle i⟩ y
  rw [hsingleMap, inner_smul_left, lp.inner_single_left, lp.inner_single_left] at heq
  simpa only [RCLike.inner_apply, map_one, one_mul, mul_one] using heq.symm

theorem adjoint_eq_diagonal
    (H G : Hilbert ι →ₗ.[ℂ] Hilbert ι) (h : ι → ℂ)
    (hdense : Dense (H.domain : Set (Hilbert ι)))
    (hsingle : ∀ i, lp.single 2 i (1 : ℂ) ∈ H.domain)
    (hH : ∀ x : H.domain, ∀ i, H x i = h i * x.val i)
    (hG : ∀ y : G.domain, ∀ i, G y i = conj (h i) * y.val i)
    (hGdomain : ∀ y : Hilbert ι,
      y ∈ G.domain ↔ Memℓp (fun i => conj (h i) * y i) 2) :
    H.adjoint = G := by
  apply le_antisymm
  · constructor
    · intro y hy
      apply (hGdomain y).mpr
      have hm := lp.memℓp (H.adjoint ⟨y, hy⟩)
      have heq : (fun i => conj (h i) * y i) =
          (H.adjoint ⟨y, hy⟩ : ι → ℂ) := by
        funext i
        exact (adjoint_apply_coordinate H h hdense hsingle hH ⟨y, hy⟩ i).symm
      rw [heq]
      exact hm
    · intro x y hxy
      ext i
      rw [adjoint_apply_coordinate H h hdense hsingle hH x i, hG]
      rw [hxy]
  · exact LinearPMap.IsFormalAdjoint.le_adjoint hdense
      (isFormalAdjoint_diagonal H G h hH hG)

theorem isSelfAdjoint_of_real_diagonal
    (H : Hilbert ι →ₗ.[ℂ] Hilbert ι) (h : ι → ℝ)
    (hdense : Dense (H.domain : Set (Hilbert ι)))
    (hsingle : ∀ i, lp.single 2 i (1 : ℂ) ∈ H.domain)
    (hH : ∀ x : H.domain, ∀ i, H x i = (h i : ℂ) * x.val i)
    (hDomain : ∀ y : Hilbert ι,
      y ∈ H.domain ↔ Memℓp (fun i => (h i : ℂ) * y i) 2) :
    IsSelfAdjoint H := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply adjoint_eq_diagonal H H (fun i => (h i : ℂ)) hdense hsingle hH
  · simpa only [Complex.conj_ofReal] using hH
  · simpa only [Complex.conj_ofReal] using hDomain

omit [DecidableEq ι] in

theorem quadraticForm_nonneg
    (H : Hilbert ι →ₗ.[ℂ] Hilbert ι) (h : ι → ℝ)
    (hpos : ∀ i, 0 ≤ h i)
    (hH : ∀ x : H.domain, ∀ i, H x i = (h i : ℂ) * x.val i)
    (x : H.domain) : 0 ≤ (inner ℂ (x : Hilbert ι) (H x)).re := by
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro i
  rw [hH]
  change 0 ≤ (inner ℂ (x.val i) ((h i : ℂ) • x.val i)).re
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change 0 ≤ ((h i : ℂ) * ((‖x.val i‖ : ℝ) : ℂ) ^ 2).re
  norm_cast
  exact mul_nonneg (hpos i) (sq_nonneg ‖x.val i‖)

end InvariantRotation.DiagonalAdjoint

end

end OAI
