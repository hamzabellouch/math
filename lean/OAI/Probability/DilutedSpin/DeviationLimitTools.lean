import OAI.Probability.DilutedSpin.PatternComparison

namespace OAI

section
namespace DilutedSpinGlass
open Filter Set
open scoped Topology

lemma limsup_affine_bound (a b : ℕ → ℝ) (c d : ℝ) (hc : 0≤c)
    (ha : ∀ n, 0≤a n) (hb : IsBoundedUnder (·≤·) atTop b)
    (h : ∀ n, a n≤c*b n+d) : limsup a atTop≤c*limsup b atTop+d := by
  have he (ε : ℝ) (hε : 0<ε) : limsup a atTop≤c*(limsup b atTop+ε)+d := by
    apply limsup_le_of_le (IsCoboundedUnder.of_frequently_ge ((Eventually.of_forall ha).frequently))
    filter_upwards [eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε) hb] with n hn
    exact (h n).trans (add_le_add (mul_le_mul_of_nonneg_left hn.le hc) le_rfl)
  have ht : Tendsto (fun ε : ℝ => c*(limsup b atTop+ε)+d) (𝓝[>] 0)
      (𝓝 (c*limsup b atTop+d)) := by
    have hh : ContinuousAt (fun ε : ℝ => c*(limsup b atTop+ε)+d) 0 := by fun_prop
    simpa using hh.continuousWithinAt.tendsto (s := Ioi 0)
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall he)

lemma doubleLimit_young (a b : ℕ → ℕ → ℝ) (C : ℝ) (hC : 0≤C)
    (ha : ∀ L n, 0≤a L n) (hb : ∀ L, IsBoundedUnder (·≤·) atTop (b L))
    (hbound : ∀ t, 0<t → ∀ L n, a L n≤C*(b L n/(2*t)+t/2))
    (hdecay : Tendsto (fun L => limsup (b L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have hupper (t : ℝ) (ht : 0<t) (L : ℕ) :
      limsup (a L) atTop≤C*(limsup (b L) atTop/(2*t)+t/2) := by
    have hh := limsup_affine_bound (a L) (b L) (C/(2*t)) (C*t/2)
      (by positivity) (ha L) (hb L) (fun n => (hbound t ht L n).trans_eq (by ring))
    convert hh using 1
    ring
  have hnonneg (L : ℕ) : 0≤limsup (a L) atTop := by
    obtain ⟨B,hB⟩ := hb L
    have hB' : ∀ᶠ n in atTop, b L n≤B := hB
    have ha' : IsBoundedUnder (·≤·) atTop (a L) := by
      apply isBoundedUnder_of_eventually_le (a := C*(B/2+1/2))
      filter_upwards [hB'] with n hn
      apply (hbound 1 (by norm_num) L n).trans
      apply mul_le_mul_of_nonneg_left _ hC
      norm_num
      linarith
    apply le_limsup_of_le ha'
    intro x hx
    obtain ⟨n,hn⟩ := hx.exists
    exact (ha L n).trans hn
  apply squeeze_triangle_grid_zero _ (C/2) hnonneg (by positivity)
    (fun t L => C*(limsup (b L) atTop/(2*t)+t/2)) _ (fun t ht L => hupper t ht L)
  intro t ht
  convert ((hdecay.div_const (2*t)).add_const (t/2)).const_mul C using 1
  simp
  ring

end DilutedSpinGlass

end

end OAI
