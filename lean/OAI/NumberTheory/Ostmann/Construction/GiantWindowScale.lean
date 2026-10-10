import OAI.NumberTheory.Ostmann.Construction.FavorableBlockScale
import OAI.NumberTheory.Ostmann.Preliminaries.CollisionScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter Ostmann.Preliminaries

def giantWindowScale (r G L : ℝ) : ℕ := ⌈Real.exp (2*G+r*favorableBlockWidth L)⌉₊

lemma log_ceil_exp_le_add_one (E : ℝ) (hE : 0≤E) :
    Real.log (⌈Real.exp E⌉₊:ℝ)≤E+1 := by
  have he1 : 1≤Real.exp E := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hE
  have he2 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hceil := (Nat.ceil_lt_add_one (Real.exp_pos E).le).le
  have hm := mul_le_mul_of_nonneg_left he2 (Real.exp_pos E).le
  rw [← Real.exp_add] at hm
  have hb : (⌈Real.exp E⌉₊:ℝ)≤Real.exp (E+1) := by linarith
  have hpos : (0:ℝ)<⌈Real.exp E⌉₊ := (Real.exp_pos E).trans_le (Nat.le_ceil _)
  have hl := Real.log_le_log hpos hb
  rwa [Real.log_exp] at hl

lemma giantWindowScale_ge (r G L : ℝ) (hr : 0≤r) (_hG : 0≤G) :
    G≤(giantWindowScale r G L:ℝ) := by
  have hh : 0≤favorableBlockWidth L := (Real.exp_pos _).le
  have h := Real.add_one_le_exp (2*G+r*favorableBlockWidth L)
  have hc := Nat.le_ceil (Real.exp (2*G+r*favorableBlockWidth L))
  change G≤(⌈Real.exp (2*G+r*favorableBlockWidth L)⌉₊:ℝ)
  nlinarith

theorem giantWindowScale_bounds (r G L : ℝ) (hr : 4≤r) (hL : 0≤L)
    (hGlo : Real.exp ((1/20:ℝ)*L)≤G) (hGhi : G≤Real.exp ((9/10:ℝ)*L))
    (hrate : r+3≤Real.exp ((1/10:ℝ)*L)) (hwidth : 5*L≤favorableBlockWidth L) :
    0<Real.log (giantWindowScale r G L:ℝ) ∧
    Real.log (Real.log (giantWindowScale r G L:ℝ))≤L ∧
    Real.exp (G+favorableBlockWidth L)≤
      Real.sqrt (giantWindowScale r G L)/(Real.log (giantWindowScale r G L:ℝ))^5 := by
  let X := giantWindowScale r G L
  let h := favorableBlockWidth L
  let E := 2*G+r*h
  have hh : 0<h := Real.exp_pos _
  have hG : 0<G := (Real.exp_pos _).trans_le hGlo
  have hE : 0<E := by dsimp [E]; nlinarith
  have hX : Real.exp E≤(X:ℝ) := Nat.le_ceil _
  have hX1 : (1:ℝ)<X := (Real.one_lt_exp_iff.mpr hE).trans_le hX
  have hlog : 0<Real.log (X:ℝ) := Real.log_pos hX1
  have hlogupper : Real.log (X:ℝ)≤E+1 := log_ceil_exp_le_add_one E hE.le
  have hhbig : h≤Real.exp ((9/10:ℝ)*L) := Real.exp_le_exp.mpr (by nlinarith)
  have hebig : 1≤Real.exp ((9/10:ℝ)*L) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by positivity : (0:ℝ)≤(9/10:ℝ)*L)
  have hprod := mul_le_mul_of_nonneg_left hrate (Real.exp_pos ((9/10:ℝ)*L)).le
  rw [← Real.exp_add,show (9/10:ℝ)*L+(1/10:ℝ)*L=L by ring] at hprod
  have hEupper : E+1≤Real.exp L := by
    have hhscale := mul_le_mul_of_nonneg_left hhbig (show 0≤r by linarith)
    dsimp [E]
    nlinarith
  have hloglog := Real.log_le_log hlog (hlogupper.trans hEupper)
  rw [Real.log_exp] at hloglog
  have hsqrt : Real.exp (G+2*h)≤Real.sqrt (X:ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [pow_two,← Real.exp_add]
    apply le_trans _ hX
    apply Real.exp_le_exp.mpr
    dsimp [E]
    nlinarith
  have hden : (Real.log (X:ℝ))^5≤Real.exp h := by
    have heq : (Real.log (X:ℝ))^5=Real.exp (5*Real.log (Real.log (X:ℝ))) := by
      simpa only [Nat.cast_ofNat,Real.exp_log hlog] using
        (Real.exp_nat_mul (Real.log (Real.log (X:ℝ))) 5).symm
    rw [heq]
    apply Real.exp_le_exp.mpr
    change 5*L≤h at hwidth
    linarith
  refine ⟨hlog,hloglog,?_⟩
  apply (le_div_iff₀ (pow_pos hlog 5)).mpr
  calc
    _ ≤ Real.exp (G+h)*Real.exp h := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = Real.exp (G+2*h) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := hsqrt

lemma exp_mul_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun L : ℝ => Real.exp (a*L)) atTop atTop := by
  simpa using tendsto_exp_mul_div_rpow_atTop 0 a ha

theorem giantWindowScale_eventually (r : ℝ) (hr : 4≤r) (M : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ G : ℝ,
      Real.exp ((1/20:ℝ)*L)≤G → G≤Real.exp ((9/10:ℝ)*L) →
      M≤giantWindowScale r G L ∧
      0<Real.log (giantWindowScale r G L:ℝ) ∧
      Real.log (Real.log (giantWindowScale r G L:ℝ))≤L ∧
      Real.exp (G+favorableBlockWidth L)≤
        Real.sqrt (giantWindowScale r G L)/(Real.log (giantWindowScale r G L:ℝ))^5 := by
  have hg := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/20)).eventually_ge_atTop (M:ℝ)
  have hrange := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/10)).eventually_ge_atTop (r+3)
  have hw : ∀ᶠ L : ℝ in atTop, 5≤favorableBlockWidth L/L := by
    have h := (tendsto_exp_mul_div_rpow_atTop 1 (1/100) (by norm_num)).eventually_ge_atTop 5
    simpa only [Real.rpow_one,favorableBlockWidth] using h
  filter_upwards [hg,hrange,hw,eventually_ge_atTop (1:ℝ)] with L hM hR hW hL
  intro G hGlo hGhi
  have hL0 : 0<L := by linarith
  have hwidth : 5*L≤favorableBlockWidth L := (le_div_iff₀ hL0).mp hW
  have hb := giantWindowScale_bounds r G L hr hL0.le hGlo hGhi hR hwidth
  refine ⟨?_,hb⟩
  have hGG : 0≤G := (Real.exp_pos _).le.trans hGlo
  have hx := (hM.trans hGlo).trans (giantWindowScale_ge r G L (by linarith) hGG)
  exact_mod_cast hx

end Ostmann.Construction

end

end OAI
