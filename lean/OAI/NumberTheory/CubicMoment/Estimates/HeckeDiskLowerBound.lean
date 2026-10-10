import OAI.NumberTheory.CubicMoment.Estimates.AnalyticDiskLowerBound
import OAI.NumberTheory.CubicMoment.Estimates.HeckeNormalizedDisk
import OAI.NumberTheory.CubicMoment.Estimates.HeckeZeros

namespace OAI

/-! Transfer of the fixed-disk logarithmic-derivative bound to the
literal Hecke continuation, keeping the contribution of a nearby zero. -/
noncomputable section
namespace CubicFirstMoment

lemma entire_zero_order_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0=1) {ρ : ℂ} (hρ : f ρ=0) : 0 < (analyticOrderAt f ρ).toNat := by
  apply ENat.toNat_pos
  · exact (hf.analyticAt ρ).analyticOrderAt_ne_zero.mpr hρ
  · intro ht
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun z => hf.analyticAt z)).mp ht
    have := congrFun he 0
    simp only [hf0,Pi.zero_apply] at this
    exact one_ne_zero this

theorem hecke_logDeriv_real_lower_of_disk
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {B : ℝ} (hB : 1 < B) {t : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    -((diskLogDerivativeConstant/3)*Real.log B) ≤
      (logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by
  let z : ℂ := ((σ-2:ℝ):ℂ)/3
  have hc : L (2+(t:ℂ)*Complex.I) ≠ 0 :=
    heckeSeries_ne_zero hχ hχ0 hχadd hs (by simp)
  have hzN : ‖z‖ ≤ (1/2:ℝ) := by
    simp only [z,norm_div,Complex.norm_real,Real.norm_eq_abs,show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hzEq : 2+(t:ℂ)*Complex.I+3*z=(σ:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hfz : normalizedHeckeDisk L t z ≠ 0 := by
    exact div_ne_zero (by rw [hzEq]; exact heckeSeries_ne_zero hχ hχ0 hχadd hs (by simpa)) hc
  have hleft (w : ℂ) (hw : normalizedHeckeDisk L t w=0) : w.re ≤ z.re := by
    have hroot : L (2+(t:ℂ)*Complex.I+3*w)=0 := (div_eq_zero_iff.mp hw).resolve_right hc
    have hwr := heckeZero_real_le_one hχ hχ0 hχadd hs hroot
    have hwre : (2+(t:ℂ)*Complex.I+3*w).re=2+3*w.re := by simp
    have hzre : z.re=(σ-2)/3 := by simp [z]
    rw [hwre] at hwr
    rw [hzre]
    linarith
  have hd := normalized_disk_logDeriv_real_lower_bound _
    (normalizedHeckeDisk_differentiable hL t) (normalizedHeckeDisk_zero t hc)
    hB hb hzN hfz hleft
  rw [normalizedHeckeDisk_logDeriv hL t z hc,hzEq] at hd
  have hre : (3*logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re=
      3*(logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by simp
  rw [hre] at hd
  linarith

theorem hecke_logDeriv_lower_of_disk
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {B : ℝ} (hB : 1 < B) {t : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    {σ β : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hβ : (1/2:ℝ) ≤ β)
    (hzero : L ((β:ℂ)+(t:ℂ)*Complex.I)=0) :
    1/(σ-β)-(diskLogDerivativeConstant/3)*Real.log B ≤
      (logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by
  let z : ℂ := ((σ-2:ℝ):ℂ)/3
  let ρ : ℂ := ((β-2:ℝ):ℂ)/3
  have hc : L (2+(t:ℂ)*Complex.I) ≠ 0 :=
    heckeSeries_ne_zero hχ hχ0 hχadd hs (by simp)
  have hβ1 : β ≤ 1 := by
    simpa using heckeZero_real_le_one hχ hχ0 hχadd hs hzero
  have hzN : ‖z‖ ≤ (1/2:ℝ) := by
    simp only [z,norm_div,Complex.norm_real,Real.norm_eq_abs,show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hρN : ‖ρ‖ ≤ (3/4:ℝ) := by
    simp only [ρ,norm_div,Complex.norm_real,Real.norm_eq_abs,show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hzEq : 2+(t:ℂ)*Complex.I+3*z=(σ:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hρEq : 2+(t:ℂ)*Complex.I+3*ρ=(β:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [ρ]
    push_cast
    ring
  have hf := normalizedHeckeDisk_differentiable hL t
  have hf0 := normalizedHeckeDisk_zero t hc
  have hfρ : normalizedHeckeDisk L t ρ=0 := by
    simp only [normalizedHeckeDisk,hρEq,hzero,zero_div]
  have hfz : normalizedHeckeDisk L t z ≠ 0 := by
    exact div_ne_zero (by rw [hzEq]; exact heckeSeries_ne_zero hχ hχ0 hχadd hs (by simpa)) hc
  have hleft (w : ℂ) (hw : normalizedHeckeDisk L t w=0) : w.re ≤ z.re := by
    have hroot : L (2+(t:ℂ)*Complex.I+3*w)=0 := (div_eq_zero_iff.mp hw).resolve_right hc
    have hwr := heckeZero_real_le_one hχ hχ0 hχadd hs hroot
    have hwre : (2+(t:ℂ)*Complex.I+3*w).re=2+3*w.re := by simp
    have hzre : z.re=(σ-2)/3 := by simp [z]
    rw [hwre] at hwr
    rw [hzre]
    linarith
  have hd := normalized_disk_logDeriv_lower_bound _ hf hf0 hB hb hzN hfz hρN hfρ hleft
  have hn := entire_zero_order_pos hf hf0 hfρ
  have hnr : (1:ℝ) ≤ (analyticOrderAt (normalizedHeckeDisk L t) ρ).toNat := by exact_mod_cast hn
  have hr : ((z-ρ)⁻¹).re=3/(σ-β) := by
    have he : z-ρ=(((σ-β)/3:ℝ):ℂ) := by
      dsimp [z,ρ]
      push_cast
      ring
    rw [he,←Complex.ofReal_inv,Complex.ofReal_re]
    field_simp
  have hpos : 0 < σ-β := by linarith
  have hm : 3/(σ-β) ≤ ((analyticOrderAt (normalizedHeckeDisk L t) ρ).toNat:ℝ)*
      (3/(σ-β)) := le_mul_of_one_le_left (by positivity) hnr
  rw [hr,normalizedHeckeDisk_logDeriv hL t z hc,hzEq] at hd
  have hre : (3*logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re=
      3*(logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by simp
  rw [hre] at hd
  rw [show 3/(σ-β)=3*(1/(σ-β)) by ring] at hd hm
  linarith

end CubicFirstMoment

end

end OAI
