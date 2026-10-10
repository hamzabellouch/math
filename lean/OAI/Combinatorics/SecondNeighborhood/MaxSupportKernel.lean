import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic

namespace OAI

namespace SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel

open Matrix

variable {I J : Type*} [Fintype I] [Fintype J]

def SupportedOn (T : Set (I × J)) (D : Matrix I J ℝ) : Prop :=
  ∀ s j, (s, j) ∉ T → D s j = 0

theorem range_lt_range_add_single [DecidableEq I] [DecidableEq J]
    (D : Matrix I J ℝ) {x : J → ℝ} {y : I → ℝ}
    (hx : D *ᵥ x = 0) (hy : Dᵀ *ᵥ y = 0)
    (s : I) (j : J) (hxj : x j ≠ 0) (hys : y s ≠ 0) :
    LinearMap.range D.mulVecLin <
      LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin := by
  let E : Matrix I J ℝ := D + Matrix.single s j 1
  let e : I → ℝ := Pi.single s 1
  change LinearMap.range D.mulVecLin < LinearMap.range E.mulVecLin
  have hsingle (w : J → ℝ) :
      Matrix.single s j (1 : ℝ) *ᵥ w = w j • e := by
    ext i
    simp [Matrix.single_mulVec, Function.update_apply, Pi.single_apply, e]
  have hEw (w : J → ℝ) :
      E.mulVecLin w = D.mulVecLin w + w j • e := by
    change (D + Matrix.single s j (1 : ℝ)) *ᵥ w = D *ᵥ w + w j • e
    rw [Matrix.add_mulVec, hsingle]
  have hEx : E.mulVecLin x = x j • e := by
    rw [hEw]
    change D *ᵥ x + x j • e = x j • e
    rw [hx, zero_add]
  have he : e ∈ LinearMap.range E.mulVecLin := by
    have hm : x j • e ∈ LinearMap.range E.mulVecLin := ⟨x, hEx⟩
    have hs := (LinearMap.range E.mulVecLin).smul_mem (x j)⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hxj, one_smul] using hs
  have hle : LinearMap.range D.mulVecLin ≤ LinearMap.range E.mulVecLin := by
    intro z hz
    rcases hz with ⟨w, rfl⟩
    have hm : E.mulVecLin w ∈ LinearMap.range E.mulVecLin := ⟨w, rfl⟩
    have hs := (LinearMap.range E.mulVecLin).sub_mem hm
      ((LinearMap.range E.mulVecLin).smul_mem (w j) he)
    rw [hEw] at hs
    simpa only [add_sub_cancel_right] using hs
  have hnot : e ∉ LinearMap.range D.mulVecLin := by
    rintro ⟨w, hw⟩
    have ha : dotProduct y (D.mulVecLin w) = 0 := by
      change dotProduct y (D *ᵥ w) = 0
      rw [← Matrix.dotProduct_transpose_mulVec D w y, hy, dotProduct_zero]
    rw [hw] at ha
    exact hys (by simpa [e] using ha)
  exact lt_iff_le_not_ge.mpr ⟨hle, fun hge => hnot (hge he)⟩

theorem kernel_support_of_max_rank {T : Set (I × J)} {D : Matrix I J ℝ}
    (hD : SupportedOn T D)
    (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
    {x : J → ℝ} {y : I → ℝ}
    (hx : D *ᵥ x = 0) (hy : Dᵀ *ᵥ y = 0)
    {s : I} {j : J} (hsj : (s, j) ∈ T) :
    x j * y s = 0 := by
  classical
  by_contra hxy
  have hxj : x j ≠ 0 := by
    intro h
    exact hxy (by rw [h, zero_mul])
  have hys : y s ≠ 0 := by
    intro h
    exact hxy (by rw [h, mul_zero])
  have hsupport : SupportedOn T (D + Matrix.single s j (1 : ℝ)) := by
    intro i k hik
    have hne : ¬(s = i ∧ j = k) := by
      rintro ⟨rfl, rfl⟩
      exact hik hsj
    change D i k + Matrix.single s j (1 : ℝ) i k = 0
    rw [hD i k hik, Matrix.single_apply_of_ne s j (1 : ℝ) i k hne, zero_add]
  have hlt : D.rank < (D + Matrix.single s j (1 : ℝ)).rank := by
    change Module.finrank ℝ (LinearMap.range D.mulVecLin) <
      Module.finrank ℝ (LinearMap.range (D + Matrix.single s j (1 : ℝ)).mulVecLin)
    exact Submodule.finrank_lt_finrank_of_lt
      (range_lt_range_add_single D hx hy s j hxj hys)
  exact (not_lt_of_ge (hmax _ hsupport)) hlt

theorem kernel_support {T : Set (I × J)} {D : Matrix I J ℝ}
    (hD : SupportedOn T D)
    (hmax : ∀ A : Matrix I J ℝ, SupportedOn T A → A.rank ≤ D.rank)
    {x : J → ℝ} {y : I → ℝ}
    (hx : x ∈ LinearMap.ker D.mulVecLin)
    (hy : y ∈ LinearMap.ker Dᵀ.mulVecLin)
    {s : I} {j : J} (hsj : (s, j) ∈ T) :
    x j * y s = 0 := by
  exact kernel_support_of_max_rank hD hmax
    (LinearMap.mem_ker.mp hx) (LinearMap.mem_ker.mp hy) hsj

end SeymourSecondNeighborhood.LinearAlgebra.MaxSupportKernel

end OAI
