import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FiniteTestHahnBanach

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma scaled_test_bound (f : StrongDual ℂ E) (A : E →L[ℂ] F)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (h : ∀ x : E,‖x‖≤1 → ‖A x‖≤δ → ‖f x‖≤ε) (x : E) :
    ‖f x‖≤ε*max ‖x‖ (‖A x‖/δ) := by
  by_cases hx : x=0
  · subst x
    simp only [map_zero,norm_zero]
    exact mul_nonneg hε.le (le_max_left _ _)
  let r : ℝ := max ‖x‖ (‖A x‖/δ)
  have hr : 0<r := lt_of_lt_of_le (norm_pos_iff.mpr hx) (le_max_left _ _)
  have hxr : ‖x‖≤r := le_max_left _ _
  have har : ‖A x‖≤δ*r := by
    have hh : ‖A x‖/δ≤r := le_max_right _ _
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  have hc : ‖((r⁻¹:ℝ):ℂ)‖=r⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have hx1 : ‖((r⁻¹:ℝ):ℂ) • x‖≤1 := by
    rw [norm_smul,hc]
    calc
      _ ≤ r⁻¹*r := mul_le_mul_of_nonneg_left hxr (le_of_lt (inv_pos.mpr hr))
      _ = 1 := inv_mul_cancel₀ hr.ne'
  have ha1 : ‖A (((r⁻¹:ℝ):ℂ) • x)‖≤δ := by
    rw [map_smul,norm_smul,hc]
    calc
      _ ≤ r⁻¹*(δ*r) := mul_le_mul_of_nonneg_left har (le_of_lt (inv_pos.mpr hr))
      _ = δ := by field_simp
  have hh := h (((r⁻¹:ℝ):ℂ) • x) hx1 ha1
  rw [map_smul,norm_smul,hc] at hh
  have ht := mul_le_mul_of_nonneg_left hh hr.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hr.ne',one_mul,mul_comm] using ht

theorem exists_approx_comp (f : StrongDual ℂ E) (A : E →L[ℂ] F)
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (h : ∀ x : E,‖x‖≤1 → ‖A x‖≤δ → ‖f x‖≤ε) :
    ∃ ψ : StrongDual ℂ F,‖f-ψ.comp A‖≤ε := by
  let g : E →L[ℂ] E×F := ((ε:ℂ) • ContinuousLinearMap.id ℂ E).prod (((ε/δ:ℝ):ℂ) • A)
  have hg (x : E) : g x=((ε:ℂ) • x,((ε/δ:ℝ):ℂ) • A x) := rfl
  have hgnorm (x : E) : ‖g x‖=ε*max ‖x‖ (‖A x‖/δ) := by
    rw [hg,Prod.norm_def]
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hε,abs_of_pos (div_pos hε hδ)]
    rw [mul_max_of_nonneg _ _ hε.le]
    congr 1
    ring
  have hgi : Function.Injective g := by
    intro x y hxy
    have hh : (ε:ℂ) • x=(ε:ℂ) • y := congrArg Prod.fst hxy
    exact (smul_right_injective E (by exact_mod_cast hε.ne')) hh
  let e := LinearEquiv.ofInjective g.toLinearMap hgi
  have heb (y : g.toLinearMap.range) : ‖f (e.symm y)‖≤‖y‖ := by
    have hh := scaled_test_bound f A hε hδ h (e.symm y)
    rw [←hgnorm] at hh
    have he : g (e.symm y)=(y:E×F) := LinearEquiv.ofInjective_symm_apply g.toLinearMap y
    rw [he] at hh
    exact hh
  let l : StrongDual ℂ g.toLinearMap.range :=
    (f.toLinearMap.comp e.symm.toLinearMap).mkContinuous 1 (by
      intro y
      change ‖f (e.symm y)‖≤1*‖y‖
      simpa only [one_mul] using heb y)
  have hln : ‖l‖≤1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  obtain ⟨G,hGe,hGn⟩ := exists_extension_norm_eq g.toLinearMap.range l
  have hG : ‖G‖≤1 := hGn.trans_le hln
  have hGg (x : E) : G (g x)=f x := by
    have hh := hGe (e x)
    change G (g x)=f (e.symm (e x)) at hh
    simpa only [LinearEquiv.symm_apply_apply] using hh
  let ψ : StrongDual ℂ F := G.comp (((ε/δ:ℝ):ℂ) • ContinuousLinearMap.inr ℂ E F)
  refine ⟨ψ,?_⟩
  apply (f-ψ.comp A).opNorm_le_bound hε.le
  intro x
  have he : (f-ψ.comp A) x=G ((ε:ℂ) • x,0) := by
    change f x-G (((ε/δ:ℝ):ℂ) • ((0:E),A x))=_
    rw [Prod.smul_mk,smul_zero]
    rw [←hGg x,hg,←map_sub]
    congr 1
    simp
  rw [he]
  calc
    _ ≤ ‖G‖*‖((ε:ℂ) • x,(0:F))‖ := G.le_opNorm _
    _ ≤ 1*‖((ε:ℂ) • x,(0:F))‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    _ = ε*‖x‖ := by
      simp [Prod.norm_def,norm_smul,abs_of_pos hε,mul_nonneg hε.le (norm_nonneg x)]

end Kadison.FiniteTestHahnBanach

end

end
end

end OAI
