import Mathlib

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace
section ReflectionTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def householder (c x : E) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {c+x}).reflection

lemma householder_apply (c x v : E) :
    householder c x v = (2 * (⟪c+x,v⟫ / ‖c+x‖ ^ 2)) • (c+x) - v := by
  rw [householder,Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, two_smul, two_mul, add_smul]

lemma householder_send {c x : E} (h : ‖c‖ = ‖x‖) : householder c x c = x := by
  have hh := Submodule.reflection_sub (v := c) (w := -x) (by simpa using h)
  rw [sub_neg_eq_add,Submodule.reflection_orthogonal_apply] at hh
  exact neg_injective hh

lemma householder_orthogonal {c x v : E} (h : ‖c‖ = ‖x‖) (hv : ⟪c,v⟫ = 0) :
    ⟪x,householder c x v⟫ = 0 := by
  calc
    ⟪x,householder c x v⟫ = ⟪householder c x c,householder c x v⟫ := by rw [householder_send h]
    _ = ⟪c,v⟫ := (householder c x).inner_map_map c v
    _ = 0 := hv

lemma householder_at_self {c v : E} (hv : ⟪c,v⟫ = 0) :
    householder c c v = -v := by
  rw [householder_apply]
  simp [inner_add_left,hv]

lemma householder_joint_continuousOn (c : E) :
    ContinuousOn (fun p : E × E => householder c p.1 p.2) {p | c+p.1 ≠ 0} := by
  have hc : Continuous (fun p : E × E => c+p.1) := continuous_const.add continuous_fst
  have hz : Continuous (fun p : E × E => p.2) := continuous_snd
  have hn : Continuous (fun p : E × E => ⟪c+p.1,p.2⟫) := hc.inner hz
  have hd : Continuous (fun p : E × E => ‖c+p.1‖ ^ 2) := hc.norm.pow 2
  have hq : ContinuousOn (fun p : E × E => ⟪c+p.1,p.2⟫ / ‖c+p.1‖ ^ 2) {p | c+p.1 ≠ 0} :=
    hn.continuousOn.div hd.continuousOn (fun _ hp => pow_ne_zero 2 (norm_ne_zero_iff.mpr hp))
  have hmul : ContinuousOn (fun p : E × E => (2 : ℝ) * (⟪c+p.1,p.2⟫ / ‖c+p.1‖ ^ 2))
      {p | c+p.1 ≠ 0} := continuous_const.continuousOn.mul hq
  have hs : ContinuousOn (fun p : E × E => ((2 : ℝ) * (⟪c+p.1,p.2⟫ / ‖c+p.1‖ ^ 2)) • (c+p.1) - p.2)
      {p | c+p.1 ≠ 0} := (hmul.smul hc.continuousOn).sub hz.continuousOn
  simpa only [householder_apply] using hs

lemma householder_joint_contDiffOn (c : E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : E × E => householder c p.1 p.2) {p | c+p.1 ≠ 0} := by
  have he : (fun p : E × E => ‖c+p.1‖ ^ 2) = fun p => ⟪c+p.1,c+p.1⟫ := by
    ext p
    exact (real_inner_self_eq_norm_sq _).symm
  simp_rw [householder_apply]
  apply ContDiffOn.sub _ contDiff_snd.contDiffOn
  apply ContDiffOn.smul _ (contDiff_const.add contDiff_fst).contDiffOn
  apply contDiff_const.contDiffOn.mul
  apply ContDiffOn.div
    (((contDiff_const.add contDiff_fst).inner ℝ contDiff_snd).contDiffOn)
    (by rw [he]; exact ((contDiff_const.add contDiff_fst).inner ℝ
      (contDiff_const.add contDiff_fst)).contDiffOn)
  intro p hp
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)

end ReflectionTransport
end BorsukNine

end OAI
