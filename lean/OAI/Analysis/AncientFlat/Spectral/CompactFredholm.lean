import Mathlib

namespace OAI
noncomputable section
open Set Module.End
namespace FlatSpectral
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma hasEigenvalue_of_mem_spectrum_compact_difference (T R : X →L[ℂ] X)
    (hK : IsCompactOperator (T-R)) (z : ℂ) (hR : z∈resolventSet ℂ R)
    (hT : z∈spectrum ℂ T) : Module.End.HasEigenvalue (T : Module.End ℂ X) z := by
  let A := X →L[ℂ] X
  have hRu : IsUnit (algebraMap ℂ A z-R) := hR
  let U : Aˣ := hRu.unit
  have hU : (U : A)=algebraMap ℂ A z-R := hRu.unit_spec
  let L : A := (T-R)*(↑U⁻¹ : A)
  have hLc : IsCompactOperator L := hK.comp_clm (↑U⁻¹ : A)
  have hfactor : (1-L)*(U : A)=algebraMap ℂ A z-T := by
    dsimp [L]
    rw [sub_mul,one_mul,mul_assoc,Units.inv_mul,mul_one,hU]
    abel
  have hLs : (1:ℂ)∈spectrum ℂ L := by
    intro hc
    have hu : IsUnit (1-L) := by simpa only [map_one] using (spectrum.mem_resolventSet_iff.mp hc)
    apply hT
    apply spectrum.mem_resolventSet_iff.mpr
    rw [←hfactor]
    exact hu.mul U.isUnit
  have hLe := (hLc.hasEigenvalue_iff_mem_spectrum (by norm_num : (1:ℂ)≠0)).mpr hLs
  obtain ⟨v,hv⟩ := hLe.exists_hasEigenvector
  let w : X := (↑U⁻¹ : A) v
  have hw : w≠0 := by
    intro hw0
    have he : (U : A) w=v := by
      change ((U : A)*(↑U⁻¹ : A)) v=v
      simp
    rw [hw0,map_zero] at he
    exact hv.2 he.symm
  have hLw : (T-R) w=v := by
    simpa only [ContinuousLinearMap.coe_coe,L,mul_apply_eq_comp,one_smul,w] using hv.apply_eq_smul
  have hUw : (algebraMap ℂ A z-R) w=v := by
    rw [←hU]
    change ((U : A)*(↑U⁻¹ : A)) v=v
    simp
  have hTw : T w=z • w := by
    have he : T w-R w=z • w-R w := by
      calc
        _=v := hLw
        _=(algebraMap ℂ A z-R) w := hUw.symm
        _=_ := rfl
    exact sub_left_injective he
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨(Module.End.mem_eigenspace_iff).mpr hTw,hw⟩
end FlatSpectral

end

end OAI
