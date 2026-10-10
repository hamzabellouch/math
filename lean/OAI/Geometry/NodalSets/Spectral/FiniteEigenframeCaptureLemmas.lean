import OAI.Geometry.NodalSets.Spectral.FiniteVariationalEigenframe

namespace OAI

noncomputable section

namespace Yau.Analysis

theorem real_symmetric_distinct_eigenvectors_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) (hs : T.IsSymmetric) (u v : E) (a b : ℝ)
    (hu : T u=a • u) (hv : T v=b • v) (hab : a ≠ b) : inner ℝ u v=0 := by
  have h : inner ℝ (T u) v = inner ℝ u (T v) := hs u v
  rw [hu,hv,inner_smul_left_eq_smul,smul_eq_mul,inner_smul_right] at h
  exact (mul_eq_zero.mp (show (a-b)*inner ℝ u v=0 by nlinarith)).resolve_left (sub_ne_zero.mpr hab)

theorem finite_eigenframe_captures_above_last {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {N : ℕ}
    (T : E →L[ℝ] E) (hs : T.IsSymmetric) (e : Fin (N+1) → E) (mu : Fin (N+1) → ℝ)
    (he : ∀ i, T (e i)=mu i • e i)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x=0) →
      inner ℝ (T x) x ≤ mu i*‖x‖^2)
    (f : E) (hf : f ≠ 0) (a : ℝ) (hfa : T f=a • f)
    (ha : mu (Fin.last N) < a) : ∃ i, mu i=a := by
  classical
  by_contra hn
  push Not at hn
  have horth (i) : inner ℝ (e i) f=0 :=
    real_symmetric_distinct_eigenvectors_orthogonal T hs (e i) f (mu i) a (he i) hfa (hn i)
  have hb := hmax (Fin.last N) f (fun j _ ↦ horth j)
  rw [hfa,inner_smul_left_eq_smul,smul_eq_mul,real_inner_self_eq_norm_sq] at hb
  have hnpos : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  exact (not_le_of_gt ha) ((mul_le_mul_iff_left₀ hnpos).mp hb)

theorem finite_frame_maximum_restrict {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {M N : ℕ} (hMN : M ≤ N)
    (T : E →L[ℝ] E) (e : Fin N → E) (mu : Fin N → ℝ)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (e j) x = 0) →
      inner ℝ (T x) x ≤ mu i * ‖x‖^2) :
    ∀ i : Fin M, ∀ x,
      (∀ j : Fin M, j < i → inner ℝ (e (Fin.castLE hMN j)) x = 0) →
      inner ℝ (T x) x ≤ mu (Fin.castLE hMN i) * ‖x‖^2 := by
  intro i x hx
  apply hmax
  intro j hj
  have hji : j.val < i.val := hj
  exact hx ⟨j.val,lt_trans hji i.isLt⟩ hji

end Yau.Analysis

end

end OAI
