import Mathlib
import OAI.Geometry.WeakMTW.Variations.GeometricFirstCut

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem segment_nonconjugacy (hMTW : HasWeakMTW (n := n) (M := M))
    (x : M) {v₀ v₁ : TangentSpace (model n) x}
    (hseg : segment ℝ v₀ v₁ ⊆ minimizingDomain x)
    (h₀ : Nonconjugate x v₀) (h₁ : Nonconjugate x v₁) :
    ∀ w ∈ segment ℝ v₀ v₁, Nonconjugate x w := by
  intro w hw
  by_cases hv : v₀ = v₁
  · subst v₁
    have : w = v₀ := by simpa only [segment_same,mem_singleton_iff] using hw
    exact this ▸ h₀
  rw [segment_eq_image'] at hw
  obtain ⟨t,ht,rfl⟩ := hw
  by_cases ht₀ : t = 0
  · simpa only [ht₀,zero_smul,add_zero] using h₀
  by_cases ht₁ : t = 1
  · simpa only [ht₁,one_smul,add_sub_cancel] using h₁
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht₀)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht₁
  let d := v₁-v₀
  let l := ‖d‖
  let p := v₀+t•d
  let e := l⁻¹•d
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hl : 0 < l := norm_pos_iff.mpr hd
  have he : inner ℝ e e = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hen : ‖e‖ = 1 := by
      rw [show e = l⁻¹•d from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hl)]
      exact inv_mul_cancel₀ hl.ne'
    rw [hen,one_pow]
  have hid (s : ℝ) : p+s•e = v₀+(t+s/l)•d := by
    dsimp only [p,e]
    rw [div_eq_mul_inv,smul_smul,add_smul,add_assoc]
  have hleft : p+(-(t*l))•e = v₀ := by
    rw [hid]
    have hsc : t+(-(t*l))/l = 0 := by field_simp; ring
    rw [hsc,zero_smul,add_zero]
  have hright : p+((1-t)*l)•e = v₁ := by
    rw [hid]
    have hsc : t+((1-t)*l)/l = 1 := by field_simp; ring
    rw [hsc,one_smul]
    exact add_sub_cancel _ _
  apply nonconjugate_middle_of_unit_segment hMTW x (mul_pos htpos hl) (mul_pos (sub_pos.mpr htlt) hl) he
  · intro s hs
    have hu : t+s/l ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have hh : -t ≤ s/l := (le_div_iff₀ hl).mpr (by nlinarith [hs.1])
        linarith
      · have hh : s/l ≤ 1-t := (div_le_iff₀ hl).mpr hs.2
        linarith
    rw [hid]
    apply hseg
    rw [segment_eq_image']
    exact ⟨t+s/l,hu,rfl⟩
  · rw [hleft]; exact h₀
  · rw [hright]; exact h₁

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
