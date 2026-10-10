import OAI.Geometry.ProjectionVolume.PolytopeFacets

namespace OAI

universe uι

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace Paper092.HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem face_vectorSpan_le_normalHyperplane (a : ι) :
    vectorSpan ℝ (P.face a) ≤ normalHyperplane (P.normal a) := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  change ⟪P.normal a, x - y⟫ = 0
  rw [inner_sub_right, hx.2, hy.2, sub_self]

theorem face_index_unique_of_finrank (a b : ι) (hne : (P.face a).Nonempty)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (P.face a)) = d - 1)
    (heq : P.face a = P.face b) : a = b := by
  have han : P.normal a ≠ 0 := by
    intro h
    have := P.normal_unit a
    simp only [h, norm_zero] at this
    norm_num at this
  have hbn : P.normal b ≠ 0 := by
    intro h
    have := P.normal_unit b
    simp only [h, norm_zero] at this
    norm_num at this
  have hWa : vectorSpan ℝ (P.face a) = normalHyperplane (P.normal a) :=
    Submodule.eq_of_le_of_finrank_eq (P.face_vectorSpan_le_normalHyperplane a)
      (hdim.trans (normalHyperplane_finrank (P.normal a) han).symm)
  have hWb : vectorSpan ℝ (P.face b) = normalHyperplane (P.normal b) :=
    Submodule.eq_of_le_of_finrank_eq (P.face_vectorSpan_le_normalHyperplane b)
      ((heq ▸ hdim).trans (normalHyperplane_finrank (P.normal b) hbn).symm)
  have hH : normalHyperplane (P.normal a) = normalHyperplane (P.normal b) := by
    rw [← hWa, ← hWb, heq]
  have hspan : Submodule.span ℝ {P.normal a} = Submodule.span ℝ {P.normal b} := by
    have h := congrArg Submodule.orthogonal hH
    simpa only [normalHyperplane, Submodule.orthogonal_orthogonal] using h
  have hbspan : P.normal b ∈ Submodule.span ℝ {P.normal a} := by
    rw [hspan]
    exact Submodule.subset_span (mem_singleton _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hbspan
  have hnorm : |c| = 1 := by
    have h := congrArg norm hc
    simpa only [norm_smul, Real.norm_eq_abs, P.normal_unit, mul_one] using h
  obtain ⟨x, hxa⟩ := hne
  have hxb : x ∈ P.face b := heq ▸ hxa
  have hoff : P.offset b = c * P.offset a := by
    rw [← hxb.2, ← hc, real_inner_smul_left, hxa.2]
  obtain ⟨p, hp⟩ := P.strict_feasible
  have haPos : 0 < P.offset a - ⟪P.normal a, p⟫ := sub_pos.mpr (hp a)
  have hbPos : 0 < c * (P.offset a - ⟪P.normal a, p⟫) := by
    have h := sub_pos.mpr (hp b)
    rwa [hoff, ← hc, real_inner_smul_left, ← mul_sub] at h
  have hcPos : 0 < c := by
    by_contra h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) haPos.le)) hbPos
  have hcOne : c = 1 := by rwa [abs_of_pos hcPos] at hnorm
  have hn : P.normal a = P.normal b := by simpa only [hcOne, one_smul] using hc
  have ho : P.offset a = P.offset b := by simpa only [hcOne, one_mul] using hoff.symm
  exact P.distinct (Prod.ext hn ho)

end Paper092.HPolytope

end

end OAI
