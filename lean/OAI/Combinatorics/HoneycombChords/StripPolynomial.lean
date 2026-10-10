import OAI.Combinatorics.HoneycombChords.StripGram
import OAI.Combinatorics.HoneycombChords.PolynomialKernels

namespace OAI

/-!
# Hyperbolic bounds for the strip density

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real MeasureTheory Filter
lemma sinh_le_mul_cosh_nonneg {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t*Real.cosh t := by
  have hd x : HasDerivAt (fun x : ℝ=>x*Real.cosh x-Real.sinh x) (x*Real.sinh x) x := by
    convert! ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1; simp only [id_eq,one_mul,add_sub_cancel_left]
  have hm : Monotone (fun x : ℝ=>x*Real.cosh x-Real.sinh x) := by
    apply monotone_of_deriv_nonneg (fun x=>(hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    rcases le_total 0 x with h|h
    · exact mul_nonneg h (Real.sinh_nonneg_iff.mpr h)
    · exact mul_nonneg_of_nonpos_of_nonpos h (Real.sinh_nonpos_iff.mpr h)
  have h:=hm ht
  simpa using h
lemma cosh_add_le_twice (a b : ℝ) : Real.cosh (a+b) ≤ 2*Real.cosh a*Real.cosh b := by
  have h:=Real.cosh_pos (a-b)
  rw [Real.cosh_add,Real.cosh_sub] at *
  linarith
lemma cosh_le_sinh_add_one {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.sinh t+1 := by
  have h : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [←Real.cosh_sub_sinh] at h
  linarith
/-- Global comparison to the exact exponential rate b=3L; no asymptotic
weight hypothesis is being postulated. -/
theorem stripDensity_sech_bounds {p : ℝ} (hp : 0 < p) :
    1/(8*angle*Real.cosh (3*angle*p)) ≤ stripDensity p ∧
    stripDensity p ≤ (p+1/angle)/Real.cosh (3*angle*p) := by
  have hL : 0 < angle := by unfold angle;positivity
  have hs : 0 < Real.sinh (4*angle*p) := Real.sinh_pos_iff.mpr (by positivity)
  have hc := Real.cosh_pos (3*angle*p)
  have hc1 := Real.one_le_cosh (angle*p)
  have ht : 0 < angle*p := mul_pos hL hp
  constructor
  · have h0:=sinh_le_mul_cosh_nonneg (show 0 ≤ 4*angle*p by positivity)
    have h1:=cosh_add_le_twice (angle*p) (3*angle*p)
    rw [show angle*p+3*angle*p=4*angle*p by ring] at h1
    have h2 : Real.sinh (4*angle*p) ≤ 8*angle*p*Real.cosh (angle*p)*Real.cosh (3*angle*p) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4*angle*p by positivity)]
    unfold stripDensity
    apply (div_le_div_iff₀ (by positivity) hs).mpr
    nlinarith [mul_nonneg (show 0 ≤ 8*angle*p*Real.cosh (3*angle*p) by positivity) (show 0 ≤ Real.cosh (angle*p)-1 by linarith)]
  · have htS : 0 < Real.sinh (angle*p) := Real.sinh_pos_iff.mpr ht
    have hadd:=Real.sinh_add (angle*p) (3*angle*p)
    have hsub:=Real.sinh_sub (3*angle*p) (angle*p)
    rw [show angle*p+3*angle*p=4*angle*p by ring] at hadd
    rw [show 3*angle*p-angle*p=2*angle*p by ring] at hsub
    have h2 : 2*Real.sinh (angle*p)*Real.cosh (3*angle*p) ≤ Real.sinh (4*angle*p) := by
      have hS := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*angle*p by positivity)
      nlinarith
    have h3:=cosh_le_sinh_add_one ht.le
    have h4:=Real.self_le_sinh_iff.mpr ht.le
    have h5 : p*Real.cosh (angle*p) ≤ (p+1/angle)*Real.sinh (angle*p) := by
      have hL1 : angle*(1/angle)=1 := by field_simp
      have hh : p ≤ Real.sinh (angle*p)/angle := (le_div_iff₀ hL).mpr (by nlinarith)
      nlinarith [mul_le_mul_of_nonneg_left h3 hp.le]
    unfold stripDensity
    apply (div_le_div_iff₀ hs hc).mpr
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ p+1/angle by positivity),
      mul_le_mul_of_nonneg_right h5 hc.le,
      mul_pos hp hc]
noncomputable def squaredPoleDensity (z p : ℝ) : ℝ := stripDensity p/(p^2+z^2)^2
lemma squaredPoleDensity_pos {z p : ℝ} (hz : 0 < z) (hp : 0 < p) : 0 < squaredPoleDensity z p := by
  unfold squaredPoleDensity
  exact div_pos (stripDensity_pos hp) (sq_pos_of_pos (by positivity))
lemma squaredPoleDensity_bounds {z Y : ℝ} (hz : 0 < z) (hzY : z ≤ Y) :
    ∃ A : ℝ,0 < A ∧ ∀ p : ℝ,0 < p →
      (1/(8*angle))/((p^2+Y^2)^2*Real.cosh (3*angle*p)) ≤ squaredPoleDensity z p ∧
      squaredPoleDensity z p ≤ A/Real.cosh (3*angle*p) := by
  have hL : 0 < angle := by unfold angle;positivity
  let A : ℝ := ((1+1/angle)/z^2+1)/z^2
  have hA : 0 < A := by dsimp [A];positivity
  refine ⟨A,hA,?_⟩
  intro p hp
  have hd : 0 < p^2+z^2 := by positivity
  have hY : 0 < Y := hz.trans_le hzY
  have hdY : 0 < p^2+Y^2 := by positivity
  have hcosh := Real.cosh_pos (3*angle*p)
  obtain ⟨hl,hu⟩:=stripDensity_sech_bounds hp
  constructor
  · have hsq : (p^2+z^2)^2 ≤ (p^2+Y^2)^2 := by gcongr
    calc
      _ = (1/(8*angle*Real.cosh (3*angle*p)))/(p^2+Y^2)^2 := by field_simp
      _  ≤  stripDensity p/(p^2+Y^2)^2 := div_le_div_of_nonneg_right hl (sq_nonneg _)
      _  ≤  squaredPoleDensity z p := div_le_div_of_nonneg_left (stripDensity_pos hp).le (sq_pos_of_pos hd) hsq
  · have hquad : p ≤ 1+p^2 := by nlinarith [sq_nonneg (p-1)]
    have hAz : 1+1/angle ≤ ((1+1/angle)/z^2+1)*z^2 := by
      have hz0 : z^2≠0 := ne_of_gt (sq_pos_of_pos hz)
      rw [add_mul,div_mul_cancel₀ _ (sq_pos_of_pos hz).ne',one_mul]
      nlinarith [sq_nonneg z]
    have hbig : p+1/angle ≤ ((1+1/angle)/z^2+1)*(p^2+z^2) := by
      have hfac : 1 ≤ (1+1/angle)/z^2+1 := by
        have hh : 0 ≤ (1+1/angle)/z^2 := by positivity
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hfac (sq_nonneg p)]
    have hnorm : (p+1/angle)/(p^2+z^2)^2 ≤ A := by
      apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
      have hcoef : 0 ≤ ((1+1/angle)/z^2+1) := by positivity
      have hadd : z^2 ≤ p^2+z^2 := by nlinarith [sq_nonneg p]
      have he : A*z^2=((1+1/angle)/z^2+1) := by dsimp [A];field_simp
      calc
        _  ≤  ((1+1/angle)/z^2+1)*(p^2+z^2) := hbig
        _ = A*z^2*(p^2+z^2) := by rw [he]
        _  ≤  A*(p^2+z^2)^2 := by nlinarith [mul_le_mul_of_nonneg_left hadd (show 0 ≤ A*(p^2+z^2) by positivity)]
    calc
      squaredPoleDensity z p  ≤  ((p+1/angle)/Real.cosh (3*angle*p))/(p^2+z^2)^2 :=
        div_le_div_of_nonneg_right hu (sq_nonneg _)
      _ = ((p+1/angle)/(p^2+z^2)^2)/Real.cosh (3*angle*p) := by ring
      _  ≤  _ := div_le_div_of_nonneg_right hnorm hcosh.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
