import OAI.NumberTheory.Ostmann.Conclusion.RegularNormCellEstimate
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior
import OAI.NumberTheory.Ostmann.Construction.NominalTotalsError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Filter
open Ostmann.Construction

theorem regular_numeric_scale_eventually (d K L₀ : ℝ) (hd : 0<d) (hK : 0<K) :
    ∀ᶠ L : ℝ in atTop, 0<L ∧
      2*Real.exp ((1/1000:ℝ)*L)/Real.exp ((1/250:ℝ)*L)≤Real.log 2 ∧
      2≤Real.exp ((1/250:ℝ)*L) ∧
      ∀ c M : ℝ, Real.exp ((1/20:ℝ)*L)-2≤c →
        c≤Real.exp ((9/10:ℝ)*L)+2 → 0≤M → M≤Real.exp (Real.exp ((3/250:ℝ)*L)) →
        L₀+1≤c ∧ 2≤c ∧ (logCellMass c ∅)⁻¹≤2*c ∧
        M≤Real.exp (d*(c-1)^(1/3:ℝ)) ∧
        2*K*c*M*Real.exp (-d*(c-1)^(1/3:ℝ))≤1 := by
  obtain ⟨c₀,hc₀⟩ := (eventually_atTop.mp logCell_normalization_eventually)
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlin : ∀ᶠ L : ℝ in atTop, L≤Real.exp ((3/250:ℝ)*L) := by
    have hh := (tendsto_exp_mul_div_rpow_atTop 1 (3/250) (by norm_num)).eventually_ge_atTop 1
    filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with L h hL
    simp only [Real.rpow_one] at h
    simpa only [one_mul] using (le_div_iff₀ hL).mp h
  filter_upwards [hlin,eventually_gt_atTop (0:ℝ),
    (exp_mul_tendsto (by norm_num : (0:ℝ)<1/500)).eventually_ge_atTop 4,
    (exp_mul_tendsto (by norm_num : (0:ℝ)<1/250)).eventually_ge_atTop (max 2 (2/d)),
    (exp_mul_tendsto (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop (4*K),
    (exp_mul_tendsto (by norm_num : (0:ℝ)<1/20)).eventually_ge_atTop (max (L₀+3) (max 4 (c₀+2))),
    (exp_mul_tendsto (by norm_num : (0:ℝ)<9/10)).eventually_ge_atTop 2,
    (exp_mul_tendsto (by norm_num : (0:ℝ)<3/1000)).eventually_ge_atTop (2/Real.log 2)]
    with L hlin hL hgap hsmall hKexp hcenter hbig hratio
  have hsm2 : 2≤Real.exp ((1/250:ℝ)*L) := (le_max_left _ _).trans hsmall
  have hsmD : 2/d≤Real.exp ((1/250:ℝ)*L) := (le_max_right _ _).trans hsmall
  refine ⟨hL,?_,hsm2,?_⟩
  · have hh := (div_le_iff₀ hlog2).mp hratio
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos ((1/1000:ℝ)*L)).le
    rw [mul_right_comm,←Real.exp_add,show (3/1000:ℝ)*L+(1/1000)*L=(1/250)*L by ring] at hm
    nlinarith
  · intro c M hclo hchi hM hMu
    have hcL : L₀+1≤c := by linarith [(le_max_left _ _).trans hcenter]
    have hc2 : 2≤c := by linarith [(le_max_left 4 (c₀+2)).trans ((le_max_right _ _).trans hcenter)]
    have hcc₀ : c₀≤c := by linarith [(le_max_right 4 (c₀+2)).trans ((le_max_right _ _).trans hcenter)]
    have hcube : Real.exp ((2/125:ℝ)*L)≤(c-1)^(1/3:ℝ) := by
      have he1 : 1≤Real.exp ((6/125:ℝ)*L) := Real.one_le_exp (by positivity)
      have hm := mul_le_mul_of_nonneg_right hgap (Real.exp_pos ((6/125:ℝ)*L)).le
      rw [←Real.exp_add,show (1/500:ℝ)*L+(6/125)*L=(1/20)*L by ring] at hm
      have hb : Real.exp ((6/125:ℝ)*L)≤c-1 := by linarith
      have hr := Real.rpow_le_rpow (Real.exp_pos _).le hb (by norm_num : (0:ℝ)≤1/3)
      rw [←Real.exp_mul,show ((6/125:ℝ)*L)*(1/3)=(2/125)*L by ring] at hr
      exact hr
    have hdcube : Real.exp ((3/250:ℝ)*L)+L≤d*(c-1)^(1/3:ℝ) := by
      have hdm := (div_le_iff₀ hd).mp hsmD
      have hm := mul_le_mul_of_nonneg_right hdm (Real.exp_pos ((3/250:ℝ)*L)).le
      rw [mul_right_comm,←Real.exp_add,show (1/250:ℝ)*L+(3/250)*L=(2/125)*L by ring] at hm
      have hh := mul_le_mul_of_nonneg_left hcube hd.le
      linarith
    have hpre : 2*K*c≤Real.exp L := by
      have hc : c≤2*Real.exp ((9/10:ℝ)*L) := by linarith
      have hm := mul_le_mul_of_nonneg_right hKexp (Real.exp_pos ((9/10:ℝ)*L)).le
      rw [←Real.exp_add,show (1/10:ℝ)*L+(9/10)*L=L by ring] at hm
      have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0≤2*K)
      linarith
    refine ⟨hcL,hc2,(hc₀ c hcc₀ ∅ (by simp)).2.2,
      hMu.trans (Real.exp_le_exp.mpr (by linarith)),?_⟩
    calc
      _ ≤ Real.exp L*Real.exp (Real.exp ((3/250:ℝ)*L))*
          Real.exp (-d*(c-1)^(1/3:ℝ)) := by gcongr
      _ = Real.exp (L+Real.exp ((3/250:ℝ)*L)-d*(c-1)^(1/3:ℝ)) := by
        rw [←Real.exp_add,←Real.exp_add]
        congr 1
        ring
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

end Ostmann.Conclusion

end

end OAI
