import OAI.Geometry.RCD.Heat.LocalSmoothLogarithmC3

namespace OAI

/-! # The finite scalar jets of a shifted logarithm

The scalar extension is used only on the nonnegative bounded value range.
Its value at zero vanishes; its first derivative there is epsilon inverse.
-/

open Set Filter
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem shifted_logarithm_jets {ε A : ℝ} (hε : 0<ε) (hA : 0≤A) :
    ∃ (F F₁ F₂ : ℝ → ℝ) (C D J B E : ℝ≥0),
      LipschitzWith C F ∧ LipschitzWith D F₁ ∧ LipschitzWith J F₂ ∧ F 0=0 ∧
      (∀ a, HasDerivAt F (F₁ a) a) ∧ (∀ a, HasDerivAt F₁ (F₂ a) a) ∧
      (∀ a, |F₁ a|≤B) ∧ (∀ a, |F₂ a|≤E) ∧
      ∀ a∈Icc 0 A, F a=Real.log (ε+a)-Real.log ε ∧
        F₁ a=(ε+a)⁻¹ ∧ F₂ a=-((ε+a)^2)⁻¹ := by
  obtain ⟨φ,ψ,χ,C,D,J,B,E,hφ,hψ,hχ,hφ0,hψ0,hdφ,hdψ,hB,hE,he⟩ :=
    exists_local_smooth_log_C3 hε (show ε≤ε+A by linarith)
  let F := fun a => φ (ε+a)-φ ε
  let F₁ := fun a => ψ (ε+a)
  let F₂ := fun a => χ (ε+a)
  have ht : LipschitzWith 1 (fun a : ℝ => ε+a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,add_sub_add_left_eq_sub,le_refl]
  have hF : LipschitzWith C F := by
    simpa only [F,Function.comp_def,mul_one,add_zero] using (hφ.comp ht).sub (LipschitzWith.const (φ ε))
  have hF₁ : LipschitzWith D F₁ := by simpa only [F₁,Function.comp_def,mul_one] using hψ.comp ht
  have hF₂ : LipschitzWith J F₂ := by simpa only [F₂,Function.comp_def,mul_one] using hχ.comp ht
  refine ⟨F,F₁,F₂,C,D,J,B,E,hF,hF₁,hF₂,?_,?_,?_,fun a => hB _,fun a => hE _,?_⟩
  · simp only [F,add_zero,sub_self]
  · intro a
    simpa only [Function.comp_def,id_eq,mul_one] using
      ((hdφ (ε+a)).comp a ((hasDerivAt_id a).const_add ε)).sub_const (φ ε)
  · intro a
    simpa only [Function.comp_def,id_eq,mul_one] using
      (hdψ (ε+a)).comp a ((hasDerivAt_id a).const_add ε)
  · intro a ha
    have h1 := he (ε+a) ⟨by linarith [ha.1],by linarith [ha.2]⟩
    have h0 := (he ε ⟨le_rfl,by linarith⟩).1
    exact ⟨by dsimp only [F]; rw [h1.1,h0],h1.2.1,h1.2.2⟩

end RegularPointCoordinates

end

end OAI
