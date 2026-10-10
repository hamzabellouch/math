import Mathlib

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter
open scoped Topology
noncomputable section

def treeError (q τ h ε εA εB δA δB : ℝ) : ℝ :=
  20*(12*q*((4*exp 1)*(4*exp 1)*ε))*h^2+
    (q*((4*exp 1)*(4*exp 1)*ε)/τ+2*exp (-q))*h+
    δA+δB+(h+1)*(12*q*((4*exp 1)*εA)+12*q*((4*exp 1)*εB))

def treeErrorEnvelope (β C x : ℝ) : ℝ :=
  240*(4*exp 1)^2*C*x^(-1998*β)+
  (4*exp 1)^2*C*x^(-1899*β)+
  2*(x^β*exp (-x))+2*C*x^(-2*β)+48*(4*exp 1)*C*x^(-1999*β)

lemma treeErrorEnvelope_tendsto (β C : ℝ) (hβ : 0<β) :
    Tendsto (treeErrorEnvelope β C) atTop (𝓝 0) := by
  have hp (a : ℝ) (ha : 0<a) : Tendsto (fun x : ℝ=>x^(-a*β)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (mul_pos ha hβ)
  have he : Tendsto (fun x : ℝ=>x^β*exp (-x)) atTop (𝓝 0) := by
    simpa only [neg_one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero β 1 (by norm_num)
  unfold treeErrorEnvelope
  simpa only [mul_zero,add_zero] using
    ((((hp 1998 (by norm_num)).const_mul (240*(4*exp 1)^2*C)).add
      ((hp 1899 (by norm_num)).const_mul ((4*exp 1)^2*C))).add
      (he.const_mul 2)).add ((hp 2 (by norm_num)).const_mul (2*C)) |>.add
      ((hp 1999 (by norm_num)).const_mul (48*(4*exp 1)*C))

lemma treeError_le_envelope {β C x q h ε εA εB δA δB : ℝ}
    (hβ : 0<β) (hC : 0≤C) (hx : 1≤x) (hq : x≤q)
    (hh0 : 0≤h) (hh : h≤x^β) (hε : 0≤ε)
    (hεA : 0≤εA) (hεB : 0≤εB)
    (he : q*ε≤C*x^(-2000*β)) (heA : q*εA≤C*x^(-2000*β))
    (heB : q*εB≤C*x^(-2000*β))
    (hdA : δA≤C*x^(-2*β)) (hdB : δB≤C*x^(-2*β)) :
    treeError q (x^(-100*β)) h ε εA εB δA δB≤treeErrorEnvelope β C x := by
  have hx0 : 0<x := by linarith
  have hq0 : 0≤q := by linarith
  have hxβ : 1≤x^β := one_le_rpow hx hβ.le
  have hexp : exp (-q)≤exp (-x) := exp_le_exp.mpr (neg_le_neg hq)
  have hfirst : 240*(4*exp 1)^2*(q*ε)*h^2≤
      240*(4*exp 1)^2*(C*x^(-2000*β))*(x^β)^2 := by
    calc
      _ ≤ 240*(4*exp 1)^2*(q*ε)*(x^β)^2 := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0 hh 2)
        exact mul_nonneg (by positivity) (mul_nonneg hq0 hε)
      _ ≤ _ := by gcongr
  have hsecond : ((4*exp 1)^2*(q*ε)/x^(-100*β))*h≤
      ((4*exp 1)^2*(C*x^(-2000*β))/x^(-100*β))*x^β := by gcongr
  have hfail : 2*exp (-q)*h≤2*exp (-x)*x^β := by gcongr
  have hlast : (h+1)*(12*(4*exp 1)*(q*εA)+12*(4*exp 1)*(q*εB))≤
      (2*x^β)*(24*(4*exp 1)*(C*x^(-2000*β))) := by
    have ha : h+1≤2*x^β := by linarith
    apply mul_le_mul ha _ (by positivity) (by positivity)
    have h1:=mul_le_mul_of_nonneg_left heA (show 0≤12*(4*exp 1) by positivity)
    have h2:=mul_le_mul_of_nonneg_left heB (show 0≤12*(4*exp 1) by positivity)
    linarith
  have p1 : x^(-2000*β)*(x^β)^2=x^(-1998*β) := by
    rw [←rpow_mul_natCast hx0.le,←rpow_add hx0]; congr 1; ring
  have p2 : x^(-2000*β)/x^(-100*β)*x^β=x^(-1899*β) := by
    rw [←rpow_sub hx0,←rpow_add hx0]; congr 1; ring
  have p3 : x^β*x^(-2000*β)=x^(-1999*β) := by
    rw [←rpow_add hx0]; congr 1; ring
  unfold treeError treeErrorEnvelope
  calc
    _ ≤ 240*(4*exp 1)^2*(C*x^(-2000*β))*(x^β)^2+
        ((4*exp 1)^2*(C*x^(-2000*β))/x^(-100*β))*x^β+
        2*exp (-x)*x^β+(C*x^(-2*β)+C*x^(-2*β))+
        (2*x^β)*(24*(4*exp 1)*(C*x^(-2000*β))) := by
      convert add_le_add (add_le_add (add_le_add (add_le_add hfirst hsecond) hfail)
        (add_le_add hdA hdB)) hlast using 1; first | rfl | ring
    _ = _ := by
      have h1 : 240*(4*exp 1)^2*(C*x^(-2000*β))*(x^β)^2=
          240*(4*exp 1)^2*C*x^(-1998*β) := by rw [←p1]; ring
      have h2 : ((4*exp 1)^2*(C*x^(-2000*β))/x^(-100*β))*x^β=
          (4*exp 1)^2*C*x^(-1899*β) := by rw [←p2]; ring
      have h3 : (2*x^β)*(24*(4*exp 1)*(C*x^(-2000*β)))=
          48*(4*exp 1)*C*x^(-1999*β) := by rw [←p3]; ring
      rw [h1,h2,h3]; ring

theorem eventually_tree_quarter (β C : ℝ) (hβ : 0<β) (hC : 0≤C) :
    ∀ᶠ x : ℝ in atTop,∀ q h ε εA εB δA δB : ℝ,
      x≤q → 0≤h → h≤x^β → 0≤ε → 0≤εA → 0≤εB →
      q*ε≤C*x^(-2000*β) → q*εA≤C*x^(-2000*β) → q*εB≤C*x^(-2000*β) →
      δA≤C*x^(-2*β) → δB≤C*x^(-2*β) →
      treeError q (x^(-100*β)) h ε εA εB δA δB≤1/4 := by
  filter_upwards [(treeErrorEnvelope_tendsto β C hβ).eventually
      (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num)),eventually_ge_atTop (1:ℝ)] with x he hx
  intro q h ε εA εB δA δB hq hh0 hh hε hεA hεB he0 heA heB hdA hdB
  exact (treeError_le_envelope hβ hC hx hq hh0 hh hε hεA hεB he0 heA heB hdA hdB).trans he.le

theorem eventually_tree_small (β C e : ℝ) (hβ : 0<β) (hC : 0≤C) (he : 0<e) :
    ∀ᶠ x : ℝ in atTop,∀ q h ε εA εB δA δB : ℝ,
      x≤q → 0≤h → h≤x^β → 0≤ε → 0≤εA → 0≤εB →
      q*ε≤C*x^(-2000*β) → q*εA≤C*x^(-2000*β) → q*εB≤C*x^(-2000*β) →
      δA≤C*x^(-2*β) → δB≤C*x^(-2*β) →
      treeError q (x^(-100*β)) h ε εA εB δA δB≤e := by
  filter_upwards [(treeErrorEnvelope_tendsto β C hβ).eventually
      (gt_mem_nhds he),eventually_ge_atTop (1:ℝ)] with x hex hx
  intro q h ε εA εB δA δB hq hh0 hh hε hεA hεB he0 heA heB hdA hdB
  exact (treeError_le_envelope hβ hC hx hq hh0 hh hε hεA hεB he0 heA heB hdA hdB).trans hex.le

end
end SharpLogRamsey.ActualPivot

end

end OAI
