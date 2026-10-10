import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonLocalRealization
open Set Metric Topology

theorem exists_local_compact_surjection (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hn : U.Nonempty) (g : C(ℂ,ℂ)) :
    ∃ f : C(ℂ,ℂ),EqOn f g Uᶜ ∧
      ∃ W : Set ℂ,IsCompact W ∧ W⊆U ∧ K⊆f '' W := by
  obtain ⟨x₀,hx₀⟩:=hn
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hU x₀ hx₀
  obtain ⟨R,hR,hbound⟩:=hK.isBounded.exists_pos_norm_le
  let s : ℝ := r/(2*R)
  have hs : 0<s := by dsimp [s]; positivity
  have hsR : s*R=r/2 := by dsimp [s]; field_simp
  let E : ℂ → ℂ := fun y=>x₀+s • y
  have he : Continuous E := continuous_const.add (continuous_id.const_smul s)
  have hEU : E '' K⊆U := by
    rintro _ ⟨y,hy,rfl⟩
    apply hball
    rw [mem_ball,dist_eq_norm]
    change ‖x₀+s • y-x₀‖<r
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left (hbound y hy) hs.le).trans_lt (by rw [hsR]; linarith)
  obtain ⟨ψ,hψ,_,hψU,_⟩:=exists_continuousMap_one_of_isCompact_subset_isOpen (hK.image he) hU hEU
  let A : ℂ → ℂ := fun x=>(s⁻¹:ℝ) • (x-x₀)
  have hA : Continuous A := (continuous_id.sub continuous_const).const_smul (s⁻¹ : ℝ)
  let f : C(ℂ,ℂ) := ⟨fun x=>(ψ x) • A x + (1-ψ x) • g x,
    (ψ.continuous.smul hA).add ((continuous_const.sub ψ.continuous).smul g.continuous)⟩
  refine ⟨f,?_,?_⟩
  · intro x hx
    have hz : ψ x=0 := by
      by_contra hn
      exact hx (hψU (subset_closure hn))
    change (ψ x) • A x + (1-ψ x) • g x=g x
    simp [hz]
  · refine ⟨E '' K,hK.image he,hEU,?_⟩
    intro y hy
    refine ⟨E y,mem_image_of_mem E hy,?_⟩
    have h1 : ψ (E y)=1 := hψ (mem_image_of_mem E hy)
    change (ψ (E y)) • A (E y) + (1-ψ (E y)) • g (E y)=y
    simp only [h1,one_smul,sub_self,zero_smul,add_zero]
    change (s⁻¹:ℝ) • (x₀+s • y-x₀)=y
    rw [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]

theorem exists_local_surjection (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hn : U.Nonempty) (g : C(ℂ,ℂ)) :
    ∃ f : C(ℂ,ℂ),EqOn f g Uᶜ ∧ K⊆f '' U := by
  obtain ⟨f,hf,W,_,hWU,hW⟩:=exists_local_compact_surjection K U hK hU hn g
  exact ⟨f,hf,hW.trans (image_mono hWU)⟩
end CannonLocalRealization

end
end
end
end

end OAI
