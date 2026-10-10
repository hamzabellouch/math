import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusNonresonance

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

def torusSize (h : Fin 2 → ℤ) : ℝ := |(h 0:ℝ)|+|(h 1:ℝ)|
def torusRate (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) : ℝ := √(torusQuadratic s h)

lemma torusSize_nonneg (h : Fin 2 → ℤ) : 0≤torusSize h := by unfold torusSize; positivity

lemma torusRate_lower {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (h : Fin 2 → ℤ) : torusSize h/2 ≤ torusRate s h := by
  have hq := hs (h 0) (h 1)
  change (1/2)*((h 0:ℝ)^2+(h 1:ℝ)^2) ≤ torusQuadratic s h at hq
  have hq0 : 0≤torusQuadratic s h := le_trans (by positivity) hq
  have hr := Real.sq_sqrt hq0
  have h0 := Real.sqrt_nonneg (torusQuadratic s h)
  have ha := sq_abs (h 0:ℝ)
  have hb := sq_abs (h 1:ℝ)
  have hab := sq_nonneg (|(h 0:ℝ)|-|(h 1:ℝ)|)
  dsimp [torusSize,torusRate]
  nlinarith [abs_nonneg (h 0:ℝ),abs_nonneg (h 1:ℝ)]

lemma int_exp_summable {r : ℝ} (hr : 0<r) :
    Summable (fun z : ℤ => exp (-r*|(z:ℝ)|)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hn : Summable (fun n : ℕ => exp (-r*(n:ℝ))) := by
    simpa only [mul_comm (-r)] using summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hr)
  constructor <;> simpa using hn

lemma torus_exp_summable {r : ℝ} (hr : 0<r) :
    Summable (fun h : Fin 2 → ℤ => exp (-r*torusSize h)) := by
  have h := (int_exp_summable hr).mul_of_nonneg (int_exp_summable hr)
    (fun _ => exp_nonneg _) (fun _ => exp_nonneg _)
  have hh := (finTwoArrowEquiv ℤ).summable_iff.mpr h
  convert hh using 1
  ext q
  simp only [Function.comp_def,finTwoArrowEquiv,piFinTwoEquiv,Equiv.coe_fn_mk]
  rw [torusSize,mul_add,exp_add]

lemma torusRate_exp_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {r : ℝ} (hr : 0<r) : Summable (fun h => exp (-r*torusRate s h)) := by
  refine (torus_exp_summable (show 0<r/2 by positivity)).of_nonneg_of_le
    (fun _ => exp_nonneg _) (fun h => ?_)
  apply exp_le_exp.mpr
  have := mul_le_mul_of_nonpos_left (torusRate_lower hs h) (by linarith : -r≤0)
  linarith

lemma pow_mul_exp_bound (n : ℕ) {r x : ℝ} (hr : 0<r) (hx : 0≤x) :
    x^n * exp (-r*x) ≤ ((n.factorial:ℝ)/(r/2)^n)*exp (-(r/2)*x) := by
  have hp : 0<(r/2)^n := pow_pos (by positivity) _
  have hf : 0<(n.factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hb := pow_div_factorial_le_exp ((r/2)*x) (mul_nonneg (by positivity) hx) n
  rw [div_le_iff₀ hf,mul_pow] at hb
  have hh : (r/2)^n*(x^n*exp (-(r/2)*x)) ≤ (n.factorial:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hb (exp_nonneg (-(r/2)*x))
    have he : exp ((r/2)*x)*exp (-(r/2)*x)=1 := by rw [←exp_add]; ring_nf; simp
    calc (r/2)^n*(x^n*exp (-(r/2)*x))
        = ((r/2)^n*x^n)*exp (-(r/2)*x) := by ring
      _ ≤ (exp ((r/2)*x)*(n.factorial:ℝ))*exp (-(r/2)*x) := hm
      _ = (n.factorial:ℝ) := by
        calc
          _ = (n.factorial:ℝ)*(exp ((r/2)*x)*exp (-(r/2)*x)) := by ring
          _ = _ := by rw [he,mul_one]
  have hh' : x^n*exp (-(r/2)*x) ≤ (n.factorial:ℝ)/(r/2)^n := by
    apply (le_div_iff₀ hp).mpr
    simpa only [mul_comm ((r/2)^n)] using hh
  have hmul := mul_le_mul_of_nonneg_right hh' (exp_nonneg (-(r/2)*x))
  calc
    x^n*exp (-r*x) = (x^n*exp (-(r/2)*x))*exp (-(r/2)*x) := by
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ _ := hmul

lemma torusRate_poly_exp_summable {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ, (1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (n : ℕ) {r : ℝ} (hr : 0<r) :
    Summable (fun h => (torusRate s h)^n*exp (-r*torusRate s h)) := by
  refine ((torusRate_exp_summable hs (show 0<r/2 by positivity)).mul_left
    ((n.factorial:ℝ)/(r/2)^n)).of_nonneg_of_le (fun h => by dsimp [torusRate]; positivity) ?_
  intro h
  exact pow_mul_exp_bound n hr (sqrt_nonneg _)

end ScalarConductivity

end

end OAI
