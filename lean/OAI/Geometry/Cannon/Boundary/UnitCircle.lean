import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
namespace CannonCircleBoundary
open Set Topology Metric
open scoped OnePoint

lemma real_interval_bounded {S : Set ℝ} (hS : IsPreconnected S)
    {b c : ℝ} (hbc : b<c) (hb : b∈closure S\S) (hc : c∈closure S\S) :
    S⊆Icc b c := by
  intro z hz
  constructor
  · by_contra h
    have hzb : z<b := lt_of_not_ge h
    obtain ⟨w,hw,hwS⟩ := (mem_closure_iff_nhds.mp hc.1) (Ioi b) (isOpen_Ioi.mem_nhds hbc)
    exact hb.2 (hS.ordConnected.out hz hwS ⟨hzb.le,hw.le⟩)
  · by_contra h
    have hcz : c<z := lt_of_not_ge h
    obtain ⟨w,hw,hwS⟩ := (mem_closure_iff_nhds.mp hb.1) (Iio c) (isOpen_Iio.mem_nhds hbc)
    exact hc.2 (hS.ordConnected.out hwS hz ⟨hw.le,hcz.le⟩)

lemma onePoint_boundary_unique {S : Set (OnePoint ℝ)} (hS : IsPreconnected S)
    (hinf : (∞ : OnePoint ℝ)∈closure S\S) {b c : ℝ}
    (hb : (b : OnePoint ℝ)∈closure S\S) (hc : (c : OnePoint ℝ)∈closure S\S) : b=c := by
  let T : Set ℝ := ((↑) : ℝ → OnePoint ℝ) ⁻¹' S
  have he : ((↑) : ℝ → OnePoint ℝ) '' T=S := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    obtain ⟨w,rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinf.2 (h ▸ hz))
    exact ⟨w,hz,rfl⟩
  have hT : IsPreconnected T := OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.mp (he ▸ hS)
  have hcl : closure T=((↑) : ℝ → OnePoint ℝ) ⁻¹' closure S := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image,he]
  have hbT : b∈closure T\T := ⟨by rw [hcl]; exact hb.1,hb.2⟩
  have hcT : c∈closure T\T := ⟨by rw [hcl]; exact hc.1,hc.2⟩
  by_contra hbc
  have hbounded : ∃ l u : ℝ,T⊆Icc l u := by
    rcases lt_or_gt_of_ne hbc with h|h
    · exact ⟨b,c,real_interval_bounded hT h hbT hcT⟩
    · exact ⟨c,b,real_interval_bounded hT h hcT hbT⟩
  obtain ⟨l,u,hlu⟩ := hbounded
  have hcompact := (isCompact_Icc (a:=l) (b:=u)).image OnePoint.continuous_coe
  have hsub : S⊆((↑) : ℝ → OnePoint ℝ) '' Icc l u := by
    rw [←he]
    exact image_mono hlu
  have hinfmem := (closure_minimal hsub hcompact.isClosed) hinf.1
  exact OnePoint.infty_notMem_image_coe hinfmem

abbrev UnitCircle := sphere (0 : ℂ) 1

def circleChart (a : UnitCircle) : OnePoint ℝ ≃ₜ UnitCircle := by
  have ha : ‖(a:ℂ)‖=1 := by simpa only [mem_sphere_zero_iff_norm] using a.property
  have hane : (a:ℂ)≠0 := by intro h; simp [h] at ha
  letI : Fact (Module.finrank ℝ ℂ=1+1) := ⟨by simp [Complex.finrank_real_complex]⟩
  have hdim : Module.finrank ℝ (ℝ ∙ (a:ℂ))ᗮ=1 :=
    Submodule.finrank_orthogonal_span_singleton (n:=1) hane
  let e : ℝ ≃L[ℝ] (ℝ ∙ (a:ℂ))ᗮ :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simpa using hdim.symm)).some
  exact e.toHomeomorph.onePointCongr.trans (onePointHyperplaneHomeoUnitSphere ha)

@[simp] lemma circleChart_infty (a : UnitCircle) : circleChart a ∞=a := by
  rfl

theorem circle_boundary_no_three {S : Set UnitCircle} (hS : IsPreconnected S)
    {a b c : UnitCircle} (ha : a∈closure S\S) (hb : b∈closure S\S)
    (hc : c∈closure S\S) (hab : a≠b) (hac : a≠c) : b=c := by
  let H := circleChart a
  let T : Set (OnePoint ℝ) := H.symm '' S
  have hT : IsPreconnected T := hS.image H.symm H.symm.continuous.continuousOn
  have hcl : closure T=H.symm '' closure S := H.symm.isClosedEmbedding.closure_image_eq S
  have hboundary {z : UnitCircle} (hz : z∈closure S\S) : H.symm z∈closure T\T := by
    refine ⟨?_,?_⟩
    · rw [hcl]; exact mem_image_of_mem _ hz.1
    · rintro ⟨w,hw,he⟩
      exact hz.2 (H.symm.injective he ▸ hw)
  have hH : H ∞=a := circleChart_infty a
  have hainf : H.symm a=∞ := H.symm_apply_eq.mpr hH.symm
  have hinf : (∞ : OnePoint ℝ)∈closure T\T := hainf ▸ hboundary ha
  have hbinf : H.symm b≠∞ := fun h => hab (H.symm.injective (hainf.trans h.symm))
  have hcinf : H.symm c≠∞ := fun h => hac (H.symm.injective (hainf.trans h.symm))
  obtain ⟨x,hx⟩ := OnePoint.ne_infty_iff_exists.mp hbinf
  obtain ⟨y,hy⟩ := OnePoint.ne_infty_iff_exists.mp hcinf
  have he := onePoint_boundary_unique hT hinf (hx.symm ▸ hboundary hb) (hy.symm ▸ hboundary hc)
  apply H.symm.injective
  rw [←hx,←hy,he]

end CannonCircleBoundary

namespace CannonCircleBoundary
open Set Topology Metric

abbrev Punctured (q : ℂ) := {z : ℂ // z≠q}

def radialDirection (q : ℂ) (z : Punctured q) : UnitCircle :=
  ⟨‖(z:ℂ)-q‖⁻¹ • ((z:ℂ)-q),by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property))⟩

lemma radialDirection_continuous (q : ℂ) : Continuous (radialDirection q) := by
  apply Continuous.subtype_mk
  have h : Continuous (fun z : Punctured q => (z:ℂ)-q) :=
    continuous_subtype_val.sub continuous_const
  exact (h.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property))).smul h

lemma radialDirection_reconstruct (q : ℂ) (z : Punctured q) :
    (z:ℂ)=q+‖(z:ℂ)-q‖ • (radialDirection q z:ℂ) := by
  have hn : ‖(z:ℂ)-q‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)
  simp only [radialDirection,smul_smul,mul_inv_cancel₀ hn,one_smul]
  abel

lemma radial_ne (q : ℂ) (u : UnitCircle) {s : ℝ} (hs : 0<s) : q+s•(u:ℂ)≠q := by
  have hu : (u:ℂ)≠0 := by
    have hh : ‖(u:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp u.property
    intro h
    simp [h] at hh
  intro he
  have h : s•(u:ℂ)=0 := add_left_cancel (he.trans (add_zero q).symm)
  exact (smul_ne_zero hs.ne' hu) h

lemma radialDirection_radial (q : ℂ) (u : UnitCircle) {s : ℝ} (hs : 0<s) :
    radialDirection q ⟨q+s•(u:ℂ),radial_ne q u hs⟩=u := by
  apply Subtype.ext
  have hu : ‖(u:ℂ)‖=1 := mem_sphere_zero_iff_norm.mp u.property
  simp only [radialDirection,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs,
    hu,mul_one,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]

theorem radial_face_degree_two {q : ℂ} {r : ℝ} {U : Set ℂ}
    (hU : IsPreconnected U) (hUball : U⊆ball q r\{q})
    (u : Fin 3 → UnitCircle)
    (hnot : ∀ i,∀ s : ℝ,0<s → s<r → q+s•(u i:ℂ)∉U)
    (hcl : ∀ i,∃ s : ℝ,0<s ∧ q+s•(u i:ℂ)∈closure U) :
    ¬Function.Injective u := by
  let V : Set (Punctured q) := Subtype.val ⁻¹' U
  have he : Subtype.val '' V=U := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    exact ⟨⟨z,(hUball hz).2⟩,hz,rfl⟩
  have hV : IsPreconnected V := IsInducing.subtypeVal.isPreconnected_image.mp (he ▸ hU)
  let S := radialDirection q '' V
  have hS : IsPreconnected S := hV.image _ (radialDirection_continuous q).continuousOn
  have hb (i : Fin 3) : u i∈closure S\S := by
    constructor
    · obtain ⟨s,hs,hsi⟩ := hcl i
      let z : Punctured q := ⟨q+s•(u i:ℂ),radial_ne q (u i) hs⟩
      have hz : z∈closure V := by
        rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,he]
        exact hsi
      have hh := mem_closure_image (radialDirection_continuous q).continuousAt hz
      rwa [radialDirection_radial q (u i) hs] at hh
    · rintro ⟨z,hz,heq⟩
      have hs : 0<‖(z:ℂ)-q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr z.property)
      have hsr : ‖(z:ℂ)-q‖<r := by simpa only [mem_ball,dist_eq_norm] using (hUball hz).1
      have hz' : q+‖(z:ℂ)-q‖•(u i:ℂ)∈U := by
        rw [←heq,←radialDirection_reconstruct q z]
        exact hz
      exact hnot i _ hs hsr hz'
  intro hu
  have hh := circle_boundary_no_three hS (hb 0) (hb 1) (hb 2)
    (hu.ne (by decide)) (hu.ne (by decide))
  exact (by decide : (1:Fin 3)≠2) (hu hh)
end CannonCircleBoundary

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
