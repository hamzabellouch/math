import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateSymmetries
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportOrder
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportDirectionCap

namespace OAI

/-! # Template symmetries preserve the positive generator-weight rays -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]

/-- The cap argument from the support-symmetries lemma: pullback of every
nonzero generator weight is a positive multiple of another generator weight.
It uses preservation of all compact convex templates, not only segments. -/
theorem templateSymmetry_weight_ray
    (D : SupportDatum W I B) (A : templateSymmetryGroup D)
    (j : I) (hj : D.weight j ≠ 0) :
    ∃ (i : I) (r : ℝ), 0 < r ∧ (D.weight j).comp A.val.toLinearMap = r • D.weight i := by
  classical
  let v : I → W := fun i => (InnerProductSpace.toDual ℝ W).symm
    (D.weight i).toContinuousLinearMap
  let β : W →ₗ[ℝ] ℝ := (D.weight j).comp A.val.toLinearMap
  let b : W := (InnerProductSpace.toDual ℝ W).symm β.toContinuousLinearMap
  have hv (i : I) (x : W) : inner ℝ (v i) x = D.weight i x :=
    InnerProductSpace.toDual_symm_apply
  have hbval (x : W) : inner ℝ b x = D.weight j (A.val x) :=
    InnerProductSpace.toDual_symm_apply
  have hb : b ≠ 0 := by
    intro hb
    apply hj
    ext x
    have hh := hbval (A.val.symm x)
    simpa only [hb, inner_zero_left, LinearEquiv.apply_symm_apply, LinearMap.zero_apply]
      using hh.symm
  by_contra hn
  have hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i := by
    intro i r hr heq
    apply hn
    refine ⟨i, r, hr, ?_⟩
    ext x
    change D.weight j (A.val x) = r * D.weight i x
    rw [← hbval, heq, real_inner_smul_left, hv]
  obtain ⟨E, hE, hne, hconv, hEK, hreach, c, hcb, hcap⟩ :=
    exists_support_direction_cap v b hb hnot
  let K := Metric.closedBall (0 : W) 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  have hbound (i : I) (x : W) (hx : x ∈ K) : D.weight i x ≤ ‖v i‖ := by
    have hx' : ‖x‖ ≤ 1 := by simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    rw [← hv]
    exact (real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (v i)])
  have hsupp (i : I) : D.weightSupport E i = D.weightSupport K i := by
    obtain ⟨x, hx, heq⟩ := hreach i
    have heq' : D.weight i x = ‖v i‖ := by rwa [hv] at heq
    have hsE := D.weightSupport_eq_of_bound_and_attained hE i ‖v i‖
      (fun y hy => hbound i y (hEK hy)) ⟨x, hx, heq'⟩
    have hsK := D.weightSupport_eq_of_bound_and_attained hK i ‖v i‖
      (hbound i) ⟨x, hEK hx, heq'⟩
    exact hsE.trans hsK.symm
  have hPE : D.templateSupport E = D.templateSupport K := by
    unfold SupportDatum.templateSupport
    congr 1
    funext k
    simp only [SupportDatum.basisTemplateSupport, hsupp]
  have hAE : IsCompact (A.val '' E) := hE.image A.val.continuous_of_finiteDimensional
  have hAK : IsCompact (A.val '' K) := hK.image A.val.continuous_of_finiteDimensional
  have hAEne : (A.val '' E).Nonempty := hne.image A.val
  have hle (i : I) : D.weightSupport (A.val '' E) i ≤ D.weightSupport (A.val '' K) i :=
    D.weightSupport_mono hAE hAEne hAK (image_mono hEK) i
  have hjE : D.weightSupport (A.val '' E) j ≤ c := by
    obtain ⟨_, ⟨x, hx, rfl⟩, heq⟩ := D.exists_weightSupport_point hAE hAEne j
    rw [heq, ← hbval]
    exact hcap x hx
  let u : W := ‖b‖⁻¹ • b
  have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have huK : u ∈ K := by
    simp [u, K, Metric.mem_closedBall, dist_zero_right, norm_smul, hbn]
  have hbu : inner ℝ b u = ‖b‖ := by
    simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hjK : ‖b‖ ≤ D.weightSupport (A.val '' K) j := by
    have hh := D.weight_le_weightSupport hAK (mem_image_of_mem A.val huK) j
    rw [← hbval, hbu] at hh
    exact hh
  have hstrict := D.templateSupport_lt_of_weightSupport hle
    ⟨j, hjE.trans_lt (hcb.trans_le hjK)⟩
  rw [A.property E hE hne hconv,
    A.property K hK hKne (convex_closedBall (0 : W) 1), hPE] at hstrict
  exact lt_irrefl _ hstrict

end PolycyclicRecognition

end

end OAI
