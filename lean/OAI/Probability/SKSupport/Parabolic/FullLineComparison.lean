import Mathlib
import OAI.Probability.SKSupport.Parabolic.ForwardConstruction

namespace OAI

section
open Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Parabolic

theorem nonnegative_fullLine_bounded
    {u ut ux uxx β c : ℝ → ℝ → ℝ} {t₀ t₁ C K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ univ))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x,
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hb : ∀ t ∈ Ioc t₀ t₁, ∀ x, β t x*x ≤ K*(1+x^2))
    (hbound : ∀ t ∈ Ioc t₀ t₁, ∀ x, c t x ≤ C)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x,
      0 ≤ ut t x-(1/2:ℝ)*uxx t x-β t x*ux t x-c t x*u t x)
    (hlower : ∀ t ∈ Icc t₀ t₁, ∀ x, -M ≤ u t x)
    (hinit : ∀ x, 0 ≤ u t₀ x) :
    ∀ t ∈ Icc t₀ t₁, ∀ x, 0 ≤ u t x := by
  let k := max C 0+2*K+2
  let E (t : ℝ) := Real.exp (-k*(t-t₀))
  have hk : 0 < k := by dsimp [k]; linarith [le_max_right C 0]
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEd (t : ℝ) : HasDerivAt E (-k*E t) t := by
    convert ((((hasDerivAt_id t).sub_const t₀).const_mul (-k)).exp) using 1 <;> dsimp [E,id]
    ring
  have hEle (t : ℝ) (ht : t ∈ Icc t₀ t₁) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sub_nonneg.mpr ht.1))
  have hperturb (ε : ℝ) (hε : 0 < ε) (t : ℝ) (htm : t ∈ Icc t₀ t₁)
      (x : ℝ) : 0 ≤ E t*u t x+ε*(1+x^2) := by
    let A := |x|+M/ε+1
    have hdiv : 0 ≤ M/ε := div_nonneg hM hε.le
    have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg x]
    have hxA : x ≤ A := by dsimp [A]; linarith [le_abs_self x]
    have hAx : -A ≤ x := by dsimp [A]; linarith [neg_abs_le x]
    have hAm : M ≤ ε*A := by
      have he : ε*(M/ε)=M := by field_simp
      dsimp [A]
      nlinarith [abs_nonneg x]
    have hAb : M ≤ ε*(1+A^2) := by
      nlinarith [mul_nonneg hε.le (sq_nonneg (A-1))]
    let V (t x : ℝ) := E t*u t x+ε*(1+x^2)
    have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc t₀ t₁ ×ˢ Icc (-A) A) := by
      apply ContinuousOn.add
      · exact (show Continuous (fun p : ℝ × ℝ => E p.1) by dsimp [E]; fun_prop).continuousOn.mul
          (hc.mono (prod_mono subset_rfl (subset_univ _)))
      · fun_prop
    have hVs (r : ℝ) (hr : r ∈ Icc t₀ t₁) : Continuous (V r) :=
      ((hs r hr).const_mul (E r)).add (by fun_prop)
    have hVt (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        HasDerivWithinAt (fun s => V s y) (E r*(ut r y-k*u r y)) (Icc t₀ t₁) r := by
      convert (((hEd r).hasDerivWithinAt.mul (ht r hr y)).add_const (ε*(1+y^2))) using 1
      ring
    have hVx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        HasDerivAt (V r) (E r*ux r y+ε*(2*y)) y := by
      convert ((hx r hr y).const_mul (E r)).add
        ((((hasDerivAt_id y).pow 2).const_add 1).const_mul ε) using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
    have hVxx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        HasDerivAt (deriv (V r)) (E r*uxx r y+2*ε) y := by
      have heloc : deriv (V r) =ᶠ[𝓝 y] (fun z => E r*deriv (u r) z+ε*(2*z)) := by
        filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
        have hp : HasDerivAt (fun z : ℝ => ε*(1+z^2)) (ε*(2*z)) z := by
          convert (((hasDerivAt_id z).pow 2).const_add 1).const_mul ε using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
        rw [(hx r hr z).deriv]
        exact (((hx r hr z).const_mul (E r)).add hp).deriv
      apply HasDerivAt.congr_of_eventuallyEq _ heloc
      convert ((hxx r hr y).const_mul (E r)).add
        (((hasDerivAt_id y).const_mul 2).const_mul ε) using 1 <;> first | rfl | ring
    have hl (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) : 0 < k-c r y := by
      have hh := hbound r hr y
      dsimp [k]
      linarith [le_max_left C 0]
    have hVp (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo (-A) A) :
        0 ≤ E r*(ut r y-k*u r y)-(1/2:ℝ)*(E r*uxx r y+2*ε)-
          β r y*(E r*ux r y+ε*(2*y))+(k-c r y)*V r y := by
      have hp := mul_nonneg (hEp r).le (hpde r hr y)
      have hc' : 2*K+2 ≤ k-c r y := by
        have hh := hbound r hr y
        dsimp [k]
        linarith [le_max_left C 0]
      have hprod := mul_le_mul_of_nonneg_right hc' (show 0 ≤ 1+y^2 by positivity)
      have hβ := hb r hr y
      have hbar : 0 ≤ (k-c r y)*(1+y^2)-1-2*β r y*y := by nlinarith [sq_nonneg y]
      have hh := mul_nonneg hε.le hbar
      dsimp [V]
      nlinarith
    have hVi (y : ℝ) (hy : y ∈ Icc (-A) A) : 0 ≤ V t₀ y := by
      exact add_nonneg (mul_nonneg (hEp t₀).le (hinit y)) (by positivity)
    have hVl (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r (-A) := by
      have hh := mul_le_mul_of_nonneg_left (hlower r hr (-A)) (hEp r).le
      have hh' := mul_le_mul_of_nonneg_right (hEle r hr) hM
      dsimp [V]
      nlinarith
    have hVr (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r A := by
      have hh := mul_le_mul_of_nonneg_left (hlower r hr A) (hEp r).le
      have hh' := mul_le_mul_of_nonneg_right (hEle r hr) hM
      dsimp [V]
      nlinarith
    exact nonnegative_of_parabolic_inequality hVc hVs hVt hVx hVxx (fun _ _ _ _ => by norm_num)
      hl hVp hVi hVl hVr t htm x ⟨hAx,hxA⟩
  intro t htt x
  have he : 0 ≤ E t*u t x := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hq : 0 < 1+x^2 := by positivity
    have hh := hperturb (δ/(1+x^2)) (div_pos hδ hq) t htt x
    simpa only [div_mul_cancel₀ _ (ne_of_gt hq)] using hh
  exact (mul_nonneg_iff_of_pos_left (hEp t)).mp he

end ZeroTemperatureSK.Parabolic

end
end
section
open Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Parabolic

theorem nonnegative_halfLine_bounded
    {u ut ux uxx β c : ℝ → ℝ → ℝ} {t₀ t₁ C K M : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc t₀ t₁ ×ˢ Ici 0))
    (hs : ∀ t ∈ Icc t₀ t₁, Continuous (u t))
    (ht : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x →
      HasDerivWithinAt (fun s => u s x) (ut t x) (Icc t₀ t₁) t)
    (hx : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x → HasDerivAt (u t) (ux t x) x)
    (hxx : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x →
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hb : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x → β t x*x ≤ K*(1+x^2))
    (hbound : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x → c t x ≤ C)
    (hpde : ∀ t ∈ Ioc t₀ t₁, ∀ x, 0 < x →
      0 ≤ ut t x-(1/2:ℝ)*uxx t x-β t x*ux t x-c t x*u t x)
    (hlower : ∀ t ∈ Icc t₀ t₁, ∀ x, 0 ≤ x → -M ≤ u t x)
    (hinit : ∀ x, 0 ≤ x → 0 ≤ u t₀ x)
    (hzero : ∀ t ∈ Icc t₀ t₁, 0 ≤ u t 0) :
    ∀ t ∈ Icc t₀ t₁, ∀ x, 0 ≤ x → 0 ≤ u t x := by
  let k := max C 0+2*K+2
  let E (t : ℝ) := Real.exp (-k*(t-t₀))
  have hk : 0 < k := by dsimp [k]; linarith [le_max_right C 0]
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEd (t : ℝ) : HasDerivAt E (-k*E t) t := by
    convert ((((hasDerivAt_id t).sub_const t₀).const_mul (-k)).exp) using 1 <;> dsimp [E,id]
    ring
  have hEle (t : ℝ) (ht : t ∈ Icc t₀ t₁) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (sub_nonneg.mpr ht.1))
  have hperturb (ε : ℝ) (hε : 0 < ε) (t : ℝ) (htm : t ∈ Icc t₀ t₁)
      (x : ℝ) (hxm : 0 ≤ x) : 0 ≤ E t*u t x+ε*(1+x^2) := by
    let A := x+M/ε+1
    have hdiv : 0 ≤ M/ε := div_nonneg hM hε.le
    have hA : 1 ≤ A := by dsimp [A]; linarith
    have hxA : x ≤ A := by dsimp [A]; linarith
    have hAm : M ≤ ε*A := by
      have he : ε*(M/ε)=M := by field_simp
      dsimp [A]
      nlinarith
    have hAb : M ≤ ε*(1+A^2) := by
      nlinarith [mul_nonneg hε.le (sq_nonneg (A-1))]
    let V (t x : ℝ) := E t*u t x+ε*(1+x^2)
    have hVc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc t₀ t₁ ×ˢ Icc 0 A) := by
      apply ContinuousOn.add
      · exact (show Continuous (fun p : ℝ × ℝ => E p.1) by dsimp [E]; fun_prop).continuousOn.mul
          (hc.mono (by intro p hp; exact ⟨hp.1,hp.2.1⟩))
      · fun_prop
    have hVs (r : ℝ) (hr : r ∈ Icc t₀ t₁) : Continuous (V r) :=
      ((hs r hr).const_mul (E r)).add (by fun_prop)
    have hVt (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        HasDerivWithinAt (fun s => V s y) (E r*(ut r y-k*u r y)) (Icc t₀ t₁) r := by
      convert (((hEd r).hasDerivWithinAt.mul (ht r hr y hy.1)).add_const (ε*(1+y^2))) using 1
      ring
    have hVx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        HasDerivAt (V r) (E r*ux r y+ε*(2*y)) y := by
      convert ((hx r hr y hy.1).const_mul (E r)).add
        ((((hasDerivAt_id y).pow 2).const_add 1).const_mul ε) using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
    have hVxx (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        HasDerivAt (deriv (V r)) (E r*uxx r y+2*ε) y := by
      have heloc : deriv (V r) =ᶠ[𝓝 y] (fun z => E r*deriv (u r) z+ε*(2*z)) := by
        filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
        have hp : HasDerivAt (fun z : ℝ => ε*(1+z^2)) (ε*(2*z)) z := by
          convert (((hasDerivAt_id z).pow 2).const_add 1).const_mul ε using 1 <;> first | rfl | ((try simp only [id_eq]); ring)
        rw [(hx r hr z hz.1).deriv]
        exact (((hx r hr z hz.1).const_mul (E r)).add hp).deriv
      apply HasDerivAt.congr_of_eventuallyEq _ heloc
      convert ((hxx r hr y hy.1).const_mul (E r)).add
        (((hasDerivAt_id y).const_mul 2).const_mul ε) using 1 <;> first | rfl | ring
    have hl (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) : 0 < k-c r y := by
      have hh := hbound r hr y hy.1
      dsimp [k]
      linarith [le_max_left C 0]
    have hVp (r : ℝ) (hr : r ∈ Ioc t₀ t₁) (y : ℝ) (hy : y ∈ Ioo 0 A) :
        0 ≤ E r*(ut r y-k*u r y)-(1/2:ℝ)*(E r*uxx r y+2*ε)-
          β r y*(E r*ux r y+ε*(2*y))+(k-c r y)*V r y := by
      have hp := mul_nonneg (hEp r).le (hpde r hr y hy.1)
      have hc' : 2*K+2 ≤ k-c r y := by
        have hh := hbound r hr y hy.1
        dsimp [k]
        linarith [le_max_left C 0]
      have hprod := mul_le_mul_of_nonneg_right hc' (show 0 ≤ 1+y^2 by positivity)
      have hβ := hb r hr y hy.1
      have hbar : 0 ≤ (k-c r y)*(1+y^2)-1-2*β r y*y := by nlinarith [sq_nonneg y]
      have hh := mul_nonneg hε.le hbar
      dsimp [V]
      nlinarith
    have hVi (y : ℝ) (hy : y ∈ Icc 0 A) : 0 ≤ V t₀ y := by
      exact add_nonneg (mul_nonneg (hEp t₀).le (hinit y hy.1)) (by positivity)
    have hVl (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r 0 := by
      exact add_nonneg (mul_nonneg (hEp r).le (hzero r hr)) (by positivity)
    have hVr (r : ℝ) (hr : r ∈ Icc t₀ t₁) : 0 ≤ V r A := by
      have hh := mul_le_mul_of_nonneg_left (hlower r hr A (by linarith)) (hEp r).le
      have hh' := mul_le_mul_of_nonneg_right (hEle r hr) hM
      dsimp [V]
      nlinarith
    exact nonnegative_of_parabolic_inequality hVc hVs hVt hVx hVxx (fun _ _ _ _ => by norm_num)
      hl hVp hVi hVl hVr t htm x ⟨hxm,hxA⟩
  intro t htt x hxx
  have he : 0 ≤ E t*u t x := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hq : 0 < 1+x^2 := by positivity
    have hh := hperturb (δ/(1+x^2)) (div_pos hδ hq) t htt x hxx
    simpa only [div_mul_cancel₀ _ (ne_of_gt hq)] using hh
  exact (mul_nonneg_iff_of_pos_left (hEp t)).mp he

end ZeroTemperatureSK.Parabolic

end
end

end OAI
