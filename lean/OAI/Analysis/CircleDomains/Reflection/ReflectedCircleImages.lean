import OAI.Analysis.CircleDomains.Reflection.ReflectedFractionalLinear
import OAI.Analysis.CircleDomains.Topology.CircleFixedEquation

namespace OAI

/-! Each boundary circle has a full round-circle image under the actual
principal map. Positivity of the radius follows from injectivity, and the
reverse inclusion follows from the exact reflected fixed-point equation. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflectedLimit_fixed_iff (D : AnalyticReflectionData C) (i : I) {z : ℂ}
    (hz : z≠D.principal (D.center i)) :
    D.reflectedLimit i z=star z ↔ D.principal.symm z∈sphere (D.center i) (D.radius i) := by
  have hi : D.principal.symm z≠D.center i := by
    intro h
    exact hz ((D.principal.apply_symm_apply z).symm.trans (congrArg D.principal h))
  rw [←roundReflectionPlane_fixed_iff (D.radius_pos i) hi]
  constructor
  · intro h
    have hh : D.principal (roundReflectionPlane (D.center i) (D.radius i)
        (D.principal.symm z))=z := star_injective h
    exact D.principal.injective (hh.trans (D.principal.apply_symm_apply z).symm)
  · intro h
    change star (D.principal (roundReflectionPlane (D.center i) (D.radius i)
      (D.principal.symm z)))=star z
    rw [h,D.principal.apply_symm_apply]

lemma exists_round_boundary_image (D : AnalyticReflectionData C) (i : I) :
    ∃s : ℝ,0<s ∧ D.principal '' sphere (D.center i) (D.radius i)=
      sphere (D.principal (D.center i)) s := by
  obtain ⟨A,_hA,hform⟩ := D.reflectedLimit_fractional_linear i
  let w : ℂ := D.center i+(D.radius i : ℂ)
  have hw : w∈sphere (D.center i) (D.radius i) := by
    simp only [mem_sphere,dist_eq_norm,w,add_sub_cancel_left,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (D.radius_pos i)]
  have hwc : w≠D.center i := by
    intro h
    have h0 : (D.radius i : ℂ)=0 := add_left_cancel (h.trans (add_zero (D.center i)).symm)
    exact (D.radius_pos i).ne' (Complex.ofReal_eq_zero.mp h0)
  let s : ℝ := ‖D.principal w-D.principal (D.center i)‖
  have hs : 0<s := norm_pos_iff.mpr (sub_ne_zero.mpr
    (fun h => hwc (D.principal.injective h)))
  have he : A=((s^2 : ℝ) : ℂ) := by
    apply (fractional_fixed_iff (fun h => hwc (D.principal.injective h))).mp
    rw [←hform _ (fun h => hwc (D.principal.injective h))]
    apply (D.reflectedLimit_fixed_iff i (fun h => hwc (D.principal.injective h))).mpr
    simpa only [D.principal.symm_apply_apply] using hw
  refine ⟨s,hs,?_⟩
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    have huc : u≠D.center i := by
      intro h
      subst u
      have h0 : (0:ℝ)=D.radius i := by simpa only [mem_sphere,dist_self] using hu
      exact (D.radius_pos i).ne' h0.symm
    have hn : D.principal u≠D.principal (D.center i) := fun h => huc (D.principal.injective h)
    have hf := (D.reflectedLimit_fixed_iff i hn).mpr
      (by simpa only [D.principal.symm_apply_apply] using hu)
    rw [hform _ hn] at hf
    have he' := (fractional_fixed_iff hn).mp hf
    have hsq : s^2=‖D.principal u-D.principal (D.center i)‖^2 := by
      exact_mod_cast he.symm.trans he'
    rw [mem_sphere,dist_eq_norm]
    nlinarith [norm_nonneg (D.principal u-D.principal (D.center i))]
  · intro hz
    have hn : z≠D.principal (D.center i) := by
      intro h
      subst z
      have h0 : (0:ℝ)=s := by simpa only [mem_sphere,dist_self] using hz
      linarith
    have hz' : ‖z-D.principal (D.center i)‖=s := by simpa only [mem_sphere,dist_eq_norm] using hz
    have hf : D.reflectedLimit i z=star z := by
      rw [hform _ hn]
      apply (fractional_fixed_iff hn).mpr
      rw [hz',he]
    exact ⟨D.principal.symm z,(D.reflectedLimit_fixed_iff i hn).mp hf,
      D.principal.apply_symm_apply z⟩

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
