import OAI.MeasureTheory.Falconer.Geometry.TwoNormalProjection
import OAI.MeasureTheory.Falconer.Geometry.NormalSeparation

namespace OAI

/-! # The intersection of two separated affine slabs lies near a codimension-two plane -/

namespace Falconer
open Set NormedSpace
variable {d : ℕ}

theorem two_slab_intersection_near_plane (u v : Space d)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {τ r : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hr : 0 ≤ r)
    (hsep : τ ≤ normalDistance u v) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∀ (p x : Space d) (a b : ℝ),
        |inner ℝ u p-a| ≤ r → |inner ℝ v p-b| ≤ r →
        |inner ℝ u x-a| ≤ r → |inner ℝ v x-b| ≤ r →
        x ∈ affineSubspaceNeighborhood V p (10*r/τ) := by
  let w := perpendicularPart u v
  have ht : τ ≤ 2*‖w‖ := hsep.trans (normalDistance_le_perpendicular hu hv)
  have hw : 0 < ‖w‖ := by linarith only [ht,hτ]
  let e := normalize w
  have he : ‖e‖ = 1 := by
    dsimp [e,NormedSpace.normalize]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw),inv_mul_cancel₀ hw.ne']
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have hwu : inner ℝ u w = 0 := by
    simp only [w,perpendicularPart,inner_sub_right,inner_smul_right,huu,mul_one,sub_self]
  have heu : inner ℝ u e = 0 := by
    simp only [e,NormedSpace.normalize,inner_smul_right,hwu,mul_zero]
  have horth : Orthonormal ℝ (![u,e] : Fin 2 → Space d) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using huu
    · simpa using heu
    · have h : inner ℝ e u = 0 := (real_inner_comm u e).trans heu
      simpa using h
    · simp [he]
  obtain ⟨V,hV,hproj⟩ := orthonormal_pair_complement _ horth
  refine ⟨V,hV,?_⟩
  intro p x a b hup hvp hux hvx
  have hdiff (n : Space d) (c : ℝ) (hp : |inner ℝ n p-c| ≤ r)
      (hx : |inner ℝ n x-c| ≤ r) : |inner ℝ n (x-p)| ≤ 2*r := by
    rw [inner_sub_right]
    have heq : inner ℝ n x-inner ℝ n p = (inner ℝ n x-c)-(inner ℝ n p-c) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by linarith only [hp,hx])
  have hudz := hdiff u a hup hux
  have hvdz := hdiff v b hvp hvx
  have hc : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  have hwdz : |inner ℝ w (x-p)| ≤ 4*r := by
    rw [show inner ℝ w (x-p) = inner ℝ v (x-p)-inner ℝ u v*inner ℝ u (x-p) by
      simp only [w,perpendicularPart,inner_sub_left,real_inner_smul_left]]
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hm := mul_le_mul hc hudz (abs_nonneg _) zero_le_one
    linarith only [hm,hvdz]
  have hedz : |inner ℝ e (x-p)| ≤ 8*r/τ := by
    change |inner ℝ (‖w‖⁻¹ • w) (x-p)| ≤ _
    rw [real_inner_smul_left,abs_mul,abs_of_pos (inv_pos.mpr hw)]
    calc
      _ ≤ ‖w‖⁻¹*(4*r) := mul_le_mul_of_nonneg_left hwdz (inv_nonneg.mpr hw.le)
      _ ≤ 8*r/τ := by
        rw [inv_mul_eq_div]
        apply (div_le_div_iff₀ hw hτ).mpr
        have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hr)
        nlinarith only [hm]
  change ‖Vᗮ.starProjection (x-p)‖ ≤ _
  have hh := hproj (x-p)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  apply hh.trans
  apply (add_le_add hudz hedz).trans
  apply (le_div_iff₀ hτ).mpr
  have hm := mul_le_mul_of_nonneg_left hτ1 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr)
  rw [add_mul,div_mul_cancel₀ _ hτ.ne']
  nlinarith only [hm]

end Falconer

end OAI
