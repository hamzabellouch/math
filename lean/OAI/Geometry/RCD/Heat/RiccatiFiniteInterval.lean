import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

namespace OAI

/-! # A finite-interval bound for a scalar Riccati inequality

A constant barrier keeps the solution above its threshold. The reciprocal
then has uniformly negative derivative, giving a bound before the endpoint.
-/

open Set
namespace RegularPointCoordinates

theorem riccati_finite_interval {Y : ℝ → ℝ} {a b A r : ℝ}
    (hab : a<b) (hA : 0<A) (hc : ContinuousOn Y (Icc a b)) (hra : r<Y a)
    (hd : ∀ x∈Ico a b, ∃ rate : ℝ, HasDerivAt Y rate x ∧
      (r≤Y x → A*(Y x-r)^2≤rate)) :
    Y a<r+1/(A*(b-a)) := by
  let c := (r+Y a)/2
  have hrc : r<c := by dsimp only [c]; linarith
  have hca : c≤Y a := by dsimp only [c]; linarith
  have hder (x : ℝ) (hx : x∈Ico a b) : HasDerivAt Y (deriv Y x) x := by
    obtain ⟨d,hd,_⟩ := hd x hx
    rwa [hd.deriv]
  have hlow (x : ℝ) (hx : x∈Ico a b) (hrx : r≤Y x) :
      A*(Y x-r)^2≤deriv Y x := by
    obtain ⟨d,hd,hb⟩ := hd x hx
    rw [hd.deriv]
    exact hb hrx
  have hstay : ∀ x∈Icc a b, c≤Y x := by
    apply image_le_of_deriv_right_lt_deriv_boundary'
      (f:=fun _ => c) (f':=fun _ => 0) (B:=Y) (B':=deriv Y)
      continuous_const.continuousOn
      (fun x _ => (hasDerivAt_const x c).hasDerivWithinAt) hca hc
      (fun x hx => (hder x hx).hasDerivWithinAt)
    intro x hx he
    have hp : 0<A*(Y x-r)^2 := mul_pos hA (sq_pos_of_pos (by rw [←he]; exact sub_pos.mpr hrc))
    exact hp.trans_le (hlow x hx (by rw [←he]; exact hrc.le))
  have hy (x : ℝ) (hx : x∈Icc a b) : 0<Y x-r := sub_pos.mpr (hrc.trans_le (hstay x hx))
  let H := fun x => 1/(Y x-r)
  have hH : ContinuousOn H (Icc a b) :=
    continuous_const.continuousOn.div (hc.sub continuous_const.continuousOn)
      (fun x hx => (hy x hx).ne')
  have hHd (x : ℝ) (hx : x∈Ioo a b) :
      HasDerivAt H (-(deriv Y x)/(Y x-r)^2) x := by
    convert ((hder x ⟨hx.1.le,hx.2⟩).sub_const r).inv
      (hy x ⟨hx.1.le,hx.2.le⟩).ne' using 1
    funext y
    simp only [H,Pi.inv_apply,one_div]
  have hbound (x : ℝ) (hx : x∈Ioo a b) : deriv H x≤-A := by
    rw [(hHd x hx).deriv]
    apply (div_le_iff₀ (sq_pos_of_pos (hy x ⟨hx.1.le,hx.2.le⟩))).mpr
    linarith only [hlow x ⟨hx.1.le,hx.2⟩ (le_of_lt (sub_pos.mp (hy x ⟨hx.1.le,hx.2.le⟩)))]
  have hi := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hH
    (by
      rw [interior_Icc]
      intro x hx
      exact (hHd x hx).differentiableAt.differentiableWithinAt)
    (by simpa only [interior_Icc] using hbound) a ⟨le_rfl,hab.le⟩ b ⟨hab.le,le_rfl⟩ hab.le
  have hp : 0<H b := one_div_pos.mpr (hy b ⟨hab.le,le_rfl⟩)
  have hrec : A*(b-a)<1/(Y a-r) := by change _-1/(Y a-r)≤_ at hi; linarith only [hi,hp]
  have hm := (lt_div_iff₀ (sub_pos.mpr hra)).mp hrec
  have hs : Y a-r<1/(A*(b-a)) :=
    (lt_div_iff₀ (mul_pos hA (sub_pos.mpr hab))).mpr (by nlinarith only [hm])
  linarith only [hs]

end RegularPointCoordinates

end OAI
