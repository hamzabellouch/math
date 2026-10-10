import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FieldSignalData

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierSignals
open Classical Set
open scoped ContDiff

theorem exists_firstBarrierSignal {R₀ R₁ : ℝ} (hR₀ : 0<R₀) (hR : R₀<R₁) :
    ∃S : FieldSignalData,S.q=-3 ∧
      (∀x,‖x‖≤R₀ → S.signal x=3) ∧ (∀x,R₁≤‖x‖ → S.signal x=-3) := by
  let b : ContDiffBump (0 : ℝ×ℝ) := ⟨R₀,R₁,hR₀,hR⟩
  let ψ : (ℝ×ℝ) → ℝ := fun x => 6*b x
  have hs : ContDiff ℝ 2 ψ := contDiff_const.mul b.contDiff
  have hc : HasCompactSupport ψ := b.hasCompactSupport.mul_left
  obtain ⟨S,hψ,hq⟩ := exists_fieldSignalData ψ hs hc (-3)
  refine ⟨S,hq,?_,?_⟩
  · intro x hx
    have hb : b x=1 := b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,b] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hb]
    norm_num
  · intro x hx
    have hb : b x=0 := b.zero_of_le_dist (by simpa only [dist_zero_right,b] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hb,mul_zero,add_zero]

theorem exists_secondBarrierSignal (ℓ : (ℝ×ℝ) →L[ℝ] ℝ) {R₁ : ℝ} (hR₁ : 0<R₁) :
    ∃S : FieldSignalData,S.q=-3 ∧
      (∀x,‖x‖≤R₁ → |ℓ x|≤1 → S.signal x=3) ∧
      (∀x,3≤|ℓ x| → S.signal x=-3) := by
  let α : ContDiffBump (0 : ℝ) := ⟨1,3,by norm_num,by norm_num⟩
  let β : ContDiffBump (0 : ℝ×ℝ) := ⟨R₁,R₁+1,hR₁,by linarith⟩
  let ψ : (ℝ×ℝ) → ℝ := fun x => 6*α (ℓ x)*β x
  have hs : ContDiff ℝ 2 ψ := (contDiff_const.mul (α.contDiff.comp ℓ.contDiff)).mul β.contDiff
  have hc : HasCompactSupport ψ := β.hasCompactSupport.mul_left
  obtain ⟨S,hψ,hq⟩ := exists_fieldSignalData ψ hs hc (-3)
  refine ⟨S,hq,?_,?_⟩
  · intro x hx hℓ
    have hα : α (ℓ x)=1 := α.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,α] using hℓ)
    have hβ : β x=1 := β.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,β] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hα,hβ]
    norm_num
  · intro x hx
    have hα : α (ℓ x)=0 := α.zero_of_le_dist (by simpa only [dist_zero_right,Real.norm_eq_abs,α] using hx)
    simp only [FieldSignalData.signal,hq,hψ,ψ,hα,mul_zero,zero_mul,add_zero]

noncomputable def conjugateLineForm (a : ℕ) (j : Fin 4) : (ℝ×ℝ) →L[ℝ] ℝ :=
  conjugate (lineNormal a j).1 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    conjugate (lineNormal a j).2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem conjugateLineForm_integral (a : ℕ) (j : Fin 4) (u : CutRing×CutRing) :
    conjugateLineForm a j (conjugate u.1,conjugate u.2)=conjugate (integralCutForm a j u) := by
  fin_cases j <;> simp [conjugateLineForm,lineNormal,integralCutForm] <;> ring

end BarrierSignals

end SimpleAmenable
end
end

end OAI
