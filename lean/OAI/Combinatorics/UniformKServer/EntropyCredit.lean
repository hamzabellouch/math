import Mathlib

namespace OAI

                                    
section

/-! Exact tangent credit for the source's multiplicative held-size tracker. -/
noncomputable section
namespace UniformKServer.EntropyCredit

def tangent (u s : ℝ) : ℝ := u-(1+Real.log u)*s

def remainder (u M x : ℝ) : ℝ := x*(Real.log x-Real.log u)-x+u-(x-u)^2/(2*M)

theorem remainder_deriv (u M x : ℝ) (hx : 0 < x) (hu : 0 < u) (hM : 0 < M) :
    HasDerivAt (remainder u M) (Real.log (x/u)-(x-u)/M) x := by
  have h := (((hasDerivAt_id x).mul ((Real.hasDerivAt_log hx.ne').sub_const (Real.log u))).sub
    (hasDerivAt_id x)).add_const u
  have hg := h.sub ((((hasDerivAt_id x).sub_const u).pow 2).div_const (2*M))
  apply hg.congr_deriv
  rw [Real.log_div hx.ne' hu.ne']
  simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,one_mul]
  field_simp
  ring

theorem credit (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
    (s-u)^2/(2*max s u) ≤ tangent u s-tangent s s := by
  by_cases hsu : s ≤ u
  · have hd (x : ℝ) (hx : x ∈ Set.Icc s u) := remainder_deriv u u x (lt_of_lt_of_le hs hx.1) hu hu
    have hc : ContinuousOn (remainder u u) (Set.Icc s u) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s u) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' := interior_subset hx
        have hp : 0 < x/u := div_pos (lt_of_lt_of_le hs hx'.1) hu
        have hl := Real.log_le_sub_one_of_pos hp
        have he : x/u-1=(x-u)/u := by field_simp
        rw [he] at hl
        linarith)
    have he := hm (show s ∈ Set.Icc s u from ⟨le_rfl,hsu⟩)
      (show u ∈ Set.Icc s u from ⟨hsu,le_rfl⟩) hsu
    simp only [remainder,sub_self,mul_zero,zero_div,zero_sub,sub_zero,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] at he
    rw [max_eq_right hsu]
    unfold tangent
    nlinarith
  · have hus := le_of_not_ge hsu
    have hd (x : ℝ) (hx : x ∈ Set.Icc u s) := remainder_deriv u s x (lt_of_lt_of_le hu hx.1) hu hs
    have hc : ContinuousOn (remainder u s) (Set.Icc u s) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc u s) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt) (fun x hx => by
        have hx' := interior_subset hx
        have hxp : 0 < x := lt_of_lt_of_le hu hx'.1
        have hl := Real.one_sub_inv_le_log_of_pos (div_pos hxp hu)
        have hk : (x-u)/s ≤ (x-u)/x := div_le_div_of_nonneg_left (sub_nonneg.mpr hx'.1) hxp hx'.2
        have he : 1-(x/u)⁻¹=(x-u)/x := by field_simp
        rw [he] at hl
        linarith)
    have he := hm (show u ∈ Set.Icc u s from ⟨le_rfl,hus⟩)
      (show s ∈ Set.Icc u s from ⟨hus,le_rfl⟩) hus
    simp only [remainder,sub_self,mul_zero,zero_div,zero_sub,sub_zero,zero_pow,
      ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] at he
    rw [max_eq_left hus]
    unfold tangent
    nlinarith


theorem relative_credit (s u : ℝ) (hs : 0 < s) (hu : 0 < u)
    (hfail : ¬ (s ≤ (6/5)*u ∧ u ≤ (6/5)*s)) :
    s+u ≤ 144*(tangent u s-tangent s s) := by
  let M := max s u
  have hM : 0 < M := lt_of_lt_of_le hs (le_max_left _ _)
  have hc := (div_le_iff₀ (show 0 < 2*M by positivity)).mp (credit s u hs hu)
  have hgap : M/6 ≤ |s-u| := by
    by_cases hsu : s ≤ u
    · have hfail' : (6/5)*s < u := by
        by_contra hh
        apply hfail
        constructor <;> nlinarith
      rw [abs_of_nonpos (sub_nonpos.mpr hsu)]
      dsimp [M]
      rw [max_eq_right hsu]
      linarith
    · have hus : u ≤ s := le_of_not_ge hsu
      have hfail' : (6/5)*u < s := by
        by_contra hh
        apply hfail
        constructor <;> nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr hus)]
      dsimp [M]
      rw [max_eq_left hus]
      linarith
  have hg := mul_self_le_mul_self (show 0 ≤ M/6 by positivity) hgap
  rw [←sq,←sq,sq_abs] at hg
  have hh : M*M ≤ (72*(tangent u s-tangent s s))*M := by nlinarith
  have hb := (mul_le_mul_iff_left₀ hM).mp hh
  have hsu : s+u ≤ 2*M := by dsimp [M]; linarith [le_max_left s u,le_max_right s u]
  linarith

end UniformKServer.EntropyCredit

end


end

end OAI
