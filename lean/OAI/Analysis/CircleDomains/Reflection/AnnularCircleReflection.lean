import OAI.Analysis.CircleDomains.Reflection.UnitCircleReflection

namespace OAI

/-! Schwarz reflection in a circle on an invariant annular neighborhood.
The reflected map is explicit, continuous and holomorphic. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

def annularCircleReflect (f:ℂ→ℂ) (z:ℂ) : ℂ :=
  if 1≤‖z‖ then f z else unitCircleReflection (f (unitCircleReflection z))

lemma continuousOn_annularCircleReflect {U:Set ℂ} {f:ℂ→ℂ}
    (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hc:ContinuousOn f (U∩{z | 1≤‖z‖}))
    (hn:∀z∈U,1≤‖z‖→f z≠0)
    (hb:∀z∈U,‖z‖=1→‖f z‖=1) :
    ContinuousOn (annularCircleReflect f) U := by
  let L := U∩{z:ℂ | ‖z‖≤1}
  have hg : ContinuousOn (fun z => f (unitCircleReflection z)) L := by
    apply hc.comp ((continuousOn_unitCircleReflection hz).mono inter_subset_left)
    intro z hzL
    exact ⟨hs z hzL.1,unitCircleReflection_outer (hz z hzL.1) hzL.2⟩
  have hg0 : ∀z∈L,f (unitCircleReflection z)≠0 := fun z hzL =>
    hn _ (hs z hzL.1) (unitCircleReflection_outer (hz z hzL.1) hzL.2)
  have hgc : ContinuousOn (fun z => unitCircleReflection (f (unitCircleReflection z))) L :=
    (continuous_conj.comp_continuousOn hg).inv₀ (fun z hzL => by simpa using hg0 z hzL)
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_if_le continuous_const (continuous_norm.comp continuous_subtype_val)
  · exact hc.comp continuous_subtype_val.continuousOn (fun z hz' => ⟨z.property,hz'⟩)
  · exact hgc.comp continuous_subtype_val.continuousOn (fun z hz' => ⟨z.property,hz'⟩)
  · intro z hz'
    have hzu : ‖(z:ℂ)‖=1 := hz'.symm
    rw [unitCircleReflection_fixed hzu,unitCircleReflection_fixed (hb z z.property hzu)]

lemma differentiableOn_annularCircleReflect {U:Set ℂ} {f:ℂ→ℂ}
    (hU:IsOpen U) (hz:∀z∈U,z≠0) (hs:∀z∈U,unitCircleReflection z∈U)
    (hc:ContinuousOn f (U∩{z | 1≤‖z‖}))
    (hd:∀z∈U,1<‖z‖→DifferentiableAt ℂ f z)
    (hn:∀z∈U,1≤‖z‖→f z≠0)
    (hb:∀z∈U,‖z‖=1→‖f z‖=1) :
    DifferentiableOn ℂ (annularCircleReflect f) U := by
  apply differentiableOn_of_continuousOn_off_unit_circle hU
    (continuousOn_annularCircleReflect hz hs hc hn hb)
  intro z hzU hzne
  rcases lt_or_gt_of_ne hzne with hsmall|hlarge
  · have he : annularCircleReflect f =ᶠ[𝓝 z]
        fun w => unitCircleReflection (f (unitCircleReflection w)) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hsmall] with w hw
      exact ite_eq_right (not_le_of_gt hw)
    apply he.differentiableAt_iff.mpr
    have href := unitCircleReflection_strict_outer (hz z hzU) hsmall
    have hfd : DifferentiableAt ℂ (fun w:ℂ => f w⁻¹) (conj z) :=
      (hd _ (hs z hzU) href).comp (conj z)
        (differentiableAt_id.inv (by simpa using hz z hzU))
    have hconj : DifferentiableAt ℂ (fun w => conj (f ((conj w)⁻¹))) z :=
      differentiableAt_conj_conj_iff.mpr hfd
    have hnonzero := hn _ (hs z hzU) href.le
    exact hconj.inv (by simpa only [unitCircleReflection,ne_eq,map_eq_zero] using hnonzero)
  · have he : annularCircleReflect f =ᶠ[𝓝 z] f := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hlarge] with w hw
      exact ite_eq_left hw.le
    exact he.differentiableAt_iff.mpr (hd z hzU hlarge)

end CircleDomainRigidity

end

end OAI
