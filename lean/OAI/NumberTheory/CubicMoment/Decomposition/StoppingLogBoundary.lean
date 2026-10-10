import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! A genuine bin boundary simultaneously preserves logarithmic
roughness in the first stage and bounds every late prime by a logarithmic
power. The choice is uniform in the geometric mesh. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem exists_geometric_boundary {ρ B Y : ℝ}
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hY : 4 ≤ Y) (hYB : Y < B) :
    ∃ h : ℕ, h < geometricBinCount ρ B ∧
      Y/4 ≤ geometricBinLower ρ B h ∧ ρ*geometricBinLower ρ B h ≤ Y := by
  have hρp : 0 < ρ := zero_lt_one.trans hρ
  have hBp : 0 < B := lt_of_lt_of_le (by norm_num) (hY.trans hYB.le)
  have hbase : B ≤ geometricBinLower ρ B 0 := by
    change B ≤ ρ^(geometricBinCount ρ B)
    apply (Real.le_pow_iff_log_le hBp hρp).mpr
    exact (div_le_iff₀ (Real.log_pos hρ)).mp (Nat.le_ceil (Real.log B/Real.log ρ))
  have hex : ∃ h : ℕ, ρ*geometricBinLower ρ B h ≤ Y := by
    refine ⟨geometricBinCount ρ B,?_⟩
    simpa only [geometricBinLower,Nat.sub_self,pow_zero,mul_one] using
      hρ₂.trans (by linarith : (2:ℝ) ≤ Y)
  let h := Nat.find hex
  have hhit : ρ*geometricBinLower ρ B h ≤ Y := Nat.find_spec hex
  have hle : h ≤ geometricBinCount ρ B := by
    apply Nat.find_min' hex
    simpa only [geometricBinLower,Nat.sub_self,pow_zero,mul_one] using
      hρ₂.trans (by linarith : (2:ℝ) ≤ Y)
  have hpos : 0 < h := by
    by_contra hn
    have he : h = 0 := by omega
    rw [he] at hhit
    have hbase' : geometricBinLower ρ B 0 < ρ*geometricBinLower ρ B 0 := by
      exact lt_mul_of_one_lt_left (pow_pos hρp _) hρ
    exact (not_lt_of_ge hhit) ((hYB.trans_le hbase).trans hbase')
  have hprev : Y < ρ*geometricBinLower ρ B (h-1) :=
    lt_of_not_ge (Nat.find_min hex (by change h-1 < h; omega))
  have hstep : geometricBinLower ρ B (h-1) = ρ*geometricBinLower ρ B h := by
    have he : geometricBinCount ρ B-(h-1) = geometricBinCount ρ B-h+1 := by omega
    simp only [geometricBinLower,he,pow_succ']
  rw [hstep] at hprev
  have hpow : 0 ≤ geometricBinLower ρ B h := pow_nonneg hρp.le _
  have hsquare : ρ*ρ ≤ 4 := by
    nlinarith [mul_self_le_mul_self hρp.le hρ₂]
  have hsmall : Y < 4*geometricBinLower ρ B h :=
    hprev.trans_le (by nlinarith [mul_le_mul_of_nonneg_right hsquare hpow])
  have hlt : h < geometricBinCount ρ B := by
    by_contra hn
    have he : h = geometricBinCount ρ B := by omega
    rw [he] at hsmall
    simp only [geometricBinLower,Nat.sub_self,pow_zero,mul_one] at hsmall
    linarith
  exact ⟨h,hlt,by linarith,hhit⟩

theorem eventually_stopping_log_boundary (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∃ h : ℕ, h < geometricBinCount ρ X ∧
        2*(Real.log X)^G ≤ geometricBinLower ρ X h ∧
          ρ*geometricBinLower ρ X h ≤ (Real.log X)^(G+4) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop ((G+4:ℕ):ℝ)
    (by norm_num : (0:ℝ) < 1)).def (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [hsmall,Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_gt_atTop (0:ℝ)] with X hsmall hL hX
  intro ρ hρ hρ₂
  have hlog : 0 ≤ Real.log X := by linarith
  have hYB : (Real.log X)^(G+4) < X := by
    have hbound : (Real.log X)^(G+4) ≤ (1/2:ℝ)*X := by
      simpa only [Real.rpow_natCast,Real.rpow_one,
        Real.norm_of_nonneg (pow_nonneg hlog _),Real.norm_of_nonneg hX.le] using hsmall
    linarith
  have hfour : (8:ℝ) ≤ (Real.log X)^4 := by
    calc
      _ ≤ (2:ℝ)^4 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  have hG : 1 ≤ (Real.log X)^G := one_le_pow₀ (by linarith)
  have hlower : 2*(Real.log X)^G ≤ (Real.log X)^(G+4)/4 := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hfour (pow_nonneg hlog G)]
  obtain ⟨h,hh,hlo,hhi⟩ := exists_geometric_boundary hρ hρ₂
    (by nlinarith : (4:ℝ) ≤ (Real.log X)^(G+4)) hYB
  exact ⟨h,hh,hlower.trans hlo,hhi⟩

theorem eventually_stopping_active_boundary {ξ : ℝ} (hξ : 0 < ξ) (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ h : ℕ, h < geometricBinCount (1+δ) X ∧
        2*(Real.log X)^G ≤ min (X^ξ) (geometricBinLower (1+δ) X h) ∧
          (1+δ)*geometricBinLower (1+δ) X h ≤ (Real.log X)^(G+4) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (G:ℝ) hξ).def
    (by norm_num : (0:ℝ) < 1/2)
  filter_upwards [eventually_stopping_log_boundary G,hsmall,
    Real.tendsto_log_atTop.eventually_ge_atTop 0,eventually_gt_atTop (0:ℝ)]
    with X hboundary hsmall hlog hX
  intro δ hδ hδone
  obtain ⟨h,hh,hlo,hhi⟩ := hboundary (1+δ) (by linarith) (by linarith)
  have hpower : 2*(Real.log X)^G ≤ X^ξ := by
    have he : (Real.log X)^G ≤ (1/2:ℝ)*X^ξ := by
      simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hlog _),
        Real.norm_of_nonneg (Real.rpow_nonneg hX.le _)] using hsmall
    linarith
  exact ⟨h,hh,le_min hpower hlo,hhi⟩

end CubicFirstMoment

end

end OAI
