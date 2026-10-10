import OAI.Geometry.TranslativeCovering.CapDisjoint

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace SlotGeometry
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

lemma ratio {n : ℕ} [NeZero n] (e f g : Sphere n)
    {l u U t r s k H K P : ℝ} (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hlr : l ≤ r) (hru : r ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) (hH : 1 ≤ H)
    {E F : Set (Sphere n)} (hE : E ⊆ cap f.val r) (hF : F ⊆ cap g.val s)
    (hraw1 : (intensity e t).real (cap f.val r) ≤ H)
    (hraw2 : (intensity e t).real (cap g.val s) ≤ H)
    (hclip1 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap f.val r)) (1/2))
    (hclip2 : Real.exp (-P*Real.log n) ≤ min ((intensity e t).real (cap g.val s)) (1/2))
    (hslot1 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap f.val r)) (1/2) ≤ (intensity e t).real E)
    (hslot2 : Real.exp (-K*Real.log n)*min ((intensity e t).real (cap g.val s)) (1/2) ≤ (intensity e t).real F) :
    (intensity e t).real (E ∩ F)/((intensity e t).real E*(intensity e t).real F) ≤
      4*H*Real.exp ((2*K+P)*Real.log n-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2) := by
  let μ := intensity e t
  let c := min (μ.real (cap f.val r)) (1/2)
  let d := min (μ.real (cap g.val s)) (1/2)
  have hc : 0 < μ.real (cap f.val r) := by
    rw [intensity_real]
    exact div_pos (cap_real_pos f ((hru.trans huU).trans_lt hU)) (cap_real_pos e ht1)
  have hd : 0 < μ.real (cap g.val s) := by
    rw [intensity_real]
    exact div_pos (cap_real_pos g ((hsu.trans huU).trans_lt hU)) (cap_real_pos e ht1)
  have hroot := DecayNormalization.sqrt_clipped hc hd hH hraw1 hraw2
  have hovering := NormalizedCaps.intensity_overlap e f g hl hU ht ht1 hlr hru hls hsu huU hk hkl hku hdim
  have hmono : μ.real (E ∩ F) ≤ μ.real (cap f.val r ∩ cap g.val s) :=
    measureReal_mono (inter_subset_inter hE hF)
  have hupper : μ.real (E ∩ F) ≤
      (4*H*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2))*Real.sqrt (c*d) := by
    have hm := mul_le_mul_of_nonneg_left hroot
      (by positivity : 0 ≤ 2*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2))
    apply (hmono.trans hovering).trans
    convert hm using 1 ; first | rfl | ring
  have hrat := CrossSlots.ratio (Real.exp_pos (-P*Real.log n)) (Real.exp_pos (-K*Real.log n))
    (by positivity : 0 ≤ 4*H*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2))
    hclip1 hclip2 hslot1 hslot2 hupper
  apply hrat.trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add,mul_div_assoc,← Real.exp_sub]
  congr 2
  ring

lemma decay {n : ℕ} {c K P C H α : ℝ} (hn : 2 ≤ n) (hlog : 0 ≤ Real.log n)
    (hc : 0 < c) (hC : 0 ≤ C) (hCn : C ≤ n) (hH : 0 ≤ H)
    (hHsq : 2*K+P+9 ≤ c*H^2) (hα : H*Real.sqrt (Real.log n/(n:ℝ)) ≤ α) :
    C*Real.exp ((2*K+P)*Real.log n-(n:ℝ)*c*α^2) ≤ (n:ℝ)⁻¹^8 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnR]
  have hs := Real.sq_sqrt (div_nonneg hlog hnp.le)
  have hα0 : 0 ≤ α := (mul_nonneg hH (Real.sqrt_nonneg _)).trans hα
  have hαsq := (sq_le_sq₀ (mul_nonneg hH (Real.sqrt_nonneg _)) hα0).mpr hα
  have hh : H^2*(Real.log n/(n:ℝ)) ≤ α^2 := by nlinarith only [hαsq,hs]
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hnp.le hc.le)
  have heq : (n:ℝ)*c*(H^2*(Real.log n/(n:ℝ))) = (c*H^2)*Real.log n := by field_simp
  rw [heq] at hm
  have hb := mul_le_mul_of_nonneg_right hHsq hlog
  have he : (2*K+P)*Real.log n-(n:ℝ)*c*α^2 ≤ -9*Real.log n := by linarith only [hb,hm]
  have hp : Real.exp (-9*Real.log n) = (n:ℝ)⁻¹^9 := by
    rw [show -9*Real.log n = -(9*Real.log n) by ring,Real.exp_neg,show (9:ℝ) = (9:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hnp,inv_pow]
  calc
    _ ≤ C*Real.exp (-9*Real.log n) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC
    _ = C*(n:ℝ)⁻¹^9 := by rw [hp]
    _ ≤ (n:ℝ)*(n:ℝ)⁻¹^9 := mul_le_mul_of_nonneg_right hCn (by positivity)
    _ = _ := by field_simp

end SlotGeometry

end OAI
