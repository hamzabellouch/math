import OAI.Analysis.FourierLLogL.Paths.Ray
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Beam

lemma prism_limits {s : Scene M} (h : Fit s) (u : Grid M) (W : Paths.Vector M)
    (a : ℝ) (z) :
    let m := matter s z; let r := prism s u W a z
    a*m ≤ r ∧ m* ‖meanV s u z‖ ≤ r := by
  intro m r
  have H := ray_bounds (W z) (letter s u z) (a*m)
  have he : letter s u z=(m:ℂ)* meanV s u z := (mean_hold s h _ _).1.symm
  constructor; exact le_trans (le_abs_self _) H.2.2.1
  rw [show m* ‖meanV s u z‖=‖letter s u z‖ by rw [he,norm_scaleC,abs_of_nonneg (matter_nonneg h z)]]
  exact H.2.1

private lemma square_addthree (x y z : ℝ) :
    (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) := by
  nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]

lemma norm_addthree (x y z : ℂ) :
    ‖x+y+z‖^2 ≤ 3*(‖x‖^2+‖y‖^2+‖z‖^2) := by
  have H : ‖x+y+z‖ ≤ ‖x‖+‖y‖+‖z‖ := (norm_add_le _ z).trans
    (add_le_add_left (norm_add_le x y) _)
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) H _) (square_addthree _ _ _)

lemma factor_swap {s q : Scene M} (hs : Fit s) (hq : Climb q)
    (u : Grid M) (z) (a : ℝ) (ha : 0 < a) (he : a ≤ 1)
    (W : Paths.Vector M) (hh : matter q z ≤ 2*matter s z) :
    let g := dew u q z; let m := mist u s q z; let r := prism s u W a z; let j := pierce q z
    ‖factor q u z‖^2 ≤ r*(8*j+32*((g+m)/a)) ∧
    (a*shell q z)^2 ≤ r*(2*j) := by
  intro g m r j
  let v := meanV s u z; let w := meanV q u z
  let x := matter s z; let y := matter q z
  let t := shell q z; let b := nub q u z
  have hN : 0 ≤ x := matter_nonneg hs z
  have hM : 0 ≤ y := matter_nonneg hq.fit z
  change y ≤ 2*x at hh
  have ht : t^2=y*j := shell_sq hq z
  have hj : 0 ≤ j := pierce_nonneg hq.fit z
  have hb : ‖b‖^2 ≤ 4*y*g := nub_innovation q hq u z
  have hg : 0 ≤ g := dew_nonneg u hq z
  have hm : 0 ≤ m := mist_nonneg u s q hq.fit z
  have hv : ‖v‖ ≤ 1 := (mean_hold _ hs _ _).2
  have hd : a*x ≤ r ∧ x* ‖v‖ ≤ r := prism_limits hs u W a z
  have hr := le_trans (mul_nonneg ha.le hN) hd.1
  have hi : x ≤ r/a := (le_div_iff₀ ha).2 (by linarith [hd.1])
  have hQ : t^2 ≤ y^2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) (shell_abs hq z) _
  constructor
  · have hx : ‖(t:ℂ)*v‖^2 ≤ 2*r*j := by
      rw [norm_scaleC,mul_pow,sq_abs,ht]
      have HE : y* ‖v‖^2 ≤ 2*r := by
        have H1 : ‖v‖^2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
        nlinarith [norm_nonneg v,hd.2]
      nlinarith [mul_le_mul_of_nonneg_right HE hj]
    have hy : ‖(t:ℂ)*(w-v)‖^2 ≤ 2*(r/a)*m := by
      rw [norm_scaleC,mul_pow,sq_abs]
      have HE : m=y*‖w-v‖^2 := rfl
      apply le_trans (mul_le_mul_of_nonneg_right hQ (sq_nonneg _))
      calc
        _= y*m := by rw [HE]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hm
    have hz : ‖b‖^2 ≤ 8*(r/a)*g := hb.trans (by nlinarith)
    rw [show factor q u z=(↑t:ℂ)*v+t*(w-v)+b by unfold t b w nub; ring]
    apply (norm_addthree _ _ _).trans
    rw [add_div,mul_add]
    nlinarith [mul_nonneg hr hj,
      mul_nonneg (div_nonneg hr ha.le) hg,mul_nonneg (div_nonneg hr ha.le) hm,
      show r*(32*(g/a+m/a))=32*(r/a)*g+32*(r/a)*m by ring]
  change (a*t)^2 ≤ _
  rw [mul_pow,ht]
  have HE : a^2*y ≤ 2*r := by nlinarith [hd.1]
  nlinarith [mul_le_mul_of_nonneg_right HE hj]

lemma bridge_mist {s : Scene M} (h : Climb s) (u z : Grid M) (i : Bool)
    {q : Scene M} (hp : Ideal (s.smaller i) q) :
    mist u s q z ≤ 8*(dew u s z + (matter (s.smaller i) z-matter q z)) := by
  let t := s.smaller i
  let v := meanV s u z; let w := meanV t u z; let l := meanV q u z
  let y := matter q z; let x := matter t z
  have H : y* ‖l-w‖^2 ≤ 4*(x-y) := (drain_changes hp u z).1
  have hH : x* ‖w-v‖^2 ≤ 2*dew u s z := mist_low u h i z
  have he : ‖l-v‖^2 ≤ 2*(‖l-w‖^2+‖w-v‖^2) := by
    have H := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (l-w) (w-v)) 2
    rw [sub_add_sub_cancel] at H
    nlinarith [sq_nonneg (‖l-w‖- ‖w-v‖)]
  have hy : 0 ≤ y := matter_nonneg hp.climb.fit z
  have hv : y ≤ x := by nlinarith
  change y* ‖l-v‖^2 ≤ 8*(_+(x-y))
  nlinarith [mul_le_mul_of_nonneg_left he hy,dew_nonneg u h z,
    mul_le_mul_of_nonneg_right hv (sq_nonneg ‖w-v‖)]

lemma extra_joints {s : Scene M} (h : Climb s) (u z : Grid M) (i : Bool)
    {q : Scene M} (hp : Ideal (s.smaller i) q) (a : ℝ) (ha : 0 < a)
    (he : a ≤ 1) (W : Paths.Vector M) :
    let t := s.smaller i
    let r := prism s u W a z; let k := matter t z-matter q z
    let j₀ := pierce s z; let j₁ := pierce q z
    let f₀ := dew u s z; let f₁ := dew u q z
    ‖factor s u z‖^2+‖factor q u z‖^2+ (a*shell s z)^2 + (a*shell q z)^2 +
      ‖letter t u z-letter q u z‖^2+(a*k)^2 ≤
         r*(20*(j₀+j₁)+400*((k+f₀+f₁)/a)) := by
  intro t r k j₀ j₁ f₀ f₁
  let x := matter s z
  have H : matter t z ≤ 2*x := matter_max h i z
  have He : ‖letter t u z-letter q u z‖ ≤ k := matter_drain hp u z
  have hk := (norm_nonneg _).trans He
  have hq : matter q z ≤ 2*x := by unfold k at hk; linarith
  have hr : 0 ≤ r := ray_pos _ _ _
  have hx : a*x ≤ r := (prism_limits h.fit u W a z).1
  have hi : k ≤ 2*(r/a) := by
    have hh : x ≤ r/a := (le_div_iff₀ ha).2 (by linarith)
    have hQ := matter_nonneg hp.climb.fit z
    change k ≥ _ at hk
    unfold k; linarith
  have hd : (a*k)^2 ≤ k^2 := pow_le_pow_left₀ (mul_nonneg ha.le hk) (by nlinarith) _
  have hh₁ := factor_swap h.fit h u z a ha he W (by linarith [matter_nonneg h.fit z])
  have HH₁ : ‖factor s u z‖^2 ≤ r*(8*j₀+32*(f₀/a)) := by
    have hH : mist u s s z=0 := by simp [mist]
    apply hh₁.1.trans
    change r*(8*j₀+32*((f₀+mist u s s z)/a)) ≤ _
    rw [hH,add_zero]
  have hh₂ := factor_swap h.fit hp.climb u z a ha he W hq
  have hh : ‖factor q u z‖^2 ≤ r*(8*j₁+32*((f₁+8*(f₀+k))/a)) := by
    have hv : mist u s q z ≤ 8*(f₀+k) := bridge_mist h u z i hp
    apply hh₂.1.trans; change r*(8*j₁+32*((f₁+mist u s q z)/a)) ≤ _
    gcongr
  have HX : (a*shell s z)^2 ≤ r*(2*j₀) := hh₁.2
  have HY : (a*shell q z)^2 ≤ r*(2*j₁) := hh₂.2
  have h₀ : 0 ≤ j₀ := pierce_nonneg h.fit z
  have h₁ : 0 ≤ j₁ := pierce_nonneg hp.climb.fit z
  have he₀ : 0 ≤ f₀ := dew_nonneg u h z
  have he₁ : 0 ≤ f₁ := dew_nonneg u hp.climb z
  have HZ := pow_le_pow_left₀ (norm_nonneg _) He 2
  simp_rw [div_eq_mul_inv] at *
  have HH := inv_pos.2 ha
  nlinarith [mul_le_mul_of_nonneg_right hi hk,
    mul_nonneg hr he₀,mul_nonneg hr he₁,mul_nonneg hr hk]

lemma contest (x y z : ℂ) (r t p : ℝ) :
    ‖x+y+z‖^2 + (r+t+p)^2 ≤
      3*((‖x‖^2+‖y‖^2+‖z‖^2)+(r^2+t^2+p^2)) := by
  linarith [square_addthree r t p,norm_addthree x y z]

end Beam


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
