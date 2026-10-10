import OAI.Geometry.NodalSets.Spectral.FiniteEigenframeCaptureLemmas

namespace OAI

namespace Yau.Analysis
noncomputable section

theorem orthonormal_indices_eq_of_common_line {E I : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : I → E) (ho : Orthonormal ℝ e) (i j : I) (f : E) (a b : ℝ)
    (hi : e i = a • f) (hj : e j = b • f) : i = j := by
  by_contra hij
  have ha : a ≠ 0 := by intro h; exact ho.ne_zero i (by rw [hi,h,zero_smul])
  have hb : b ≠ 0 := by intro h; exact ho.ne_zero j (by rw [hj,h,zero_smul])
  have hf : f ≠ 0 := by intro h; exact ho.ne_zero i (by rw [hi,h,smul_zero])
  have h := ho.inner_eq_zero hij
  rw [hi,hj,inner_smul_left_eq_smul,smul_eq_mul,inner_smul_right] at h
  exact (mul_ne_zero ha (mul_ne_zero hb ((inner_self_ne_zero (𝕜 := ℝ)).mpr hf))) h

theorem finite_eigenframe_simple_from_gap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (T : E →L[ℝ] E) (hs : T.IsSymmetric) (e : Fin N → E) (mu : Fin N → ℝ)
    (ho : Orthonormal ℝ e) (he : ∀ i, T (e i)=mu i • e i)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x=0) →
      inner ℝ (T x) x ≤ mu i*‖x‖^2)
    (i k : Fin N) (hgap : mu k < mu i)
    (hunique : ∀ j, j < k → j ≠ i → mu j ≠ mu i)
    (f : E) (hf : T f=mu i • f) :
    f = (inner ℝ (e i) f) • e i := by
  let g := f - (inner ℝ (e i) f) • e i
  have hg : T g = mu i • g := by
    simp only [g,map_sub,map_smul,hf,he,smul_sub,smul_smul]
    rw [mul_comm (inner ℝ (e i) f)]
  have hgorth : ∀ j, j < k → inner ℝ (e j) g=0 := by
    intro j hj
    by_cases hji : j=i
    · subst j
      simp only [g,inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,
        ho.norm_eq_one,one_pow,mul_one,sub_self]
    · have horth := real_symmetric_distinct_eigenvectors_orthogonal T hs (e j) f
        (mu j) (mu i) (he j) hf (hunique j hj hji)
      simp only [g,inner_sub_right,inner_smul_right,horth,ho.inner_eq_zero hji,mul_zero,sub_self]
  have hb := hmax k g hgorth
  rw [hg,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq] at hb
  have hg0 : g=0 := by
    by_contra hn
    have hp : 0 < ‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
    exact (not_le_of_gt (mul_lt_mul_of_pos_right hgap hp)) hb
  exact sub_eq_zero.mp hg0

end
end Yau.Analysis

end OAI
