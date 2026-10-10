import Mathlib
import OAI.Probability.SKValue.Gaussian.DensityJump

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SKValue
lemma derivative_parity {f g:ℝ → ℝ} {e:ℝ}
    (hd:∀ x,HasDerivAt f (g x) x) (he:∀ x,f (-x)=e*f x) (x:ℝ) :
    g (-x)= -e*g x := by
  have h1:HasDerivAt (fun y ↦ f (-y)) (-g (-x)) x := by
    convert! (hd (-x)).comp x (hasDerivAt_neg x) using 1; ring
  have h2:HasDerivAt (fun y ↦ e*f y) (e*g x) x := (hd x).const_mul e
  have hh:(fun y ↦ f (-y))=(fun y ↦ e*f y) := funext he
  rw [hh] at h1
  have hh' := h1.unique h2
  linarith

lemma SmoothTerminal.spatialJet_space {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) (x:ℝ) :
    HasDerivAt (spatialJet c A n) (spatialJet c A (n+1) x) x := by
  have hd := (hA.jets.smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  exact hd.const_mul c

lemma SmoothTerminal.spatialJet_growth {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) : ExpGrowth (spatialJet c A n) := by
  obtain ⟨C,hC,hb⟩ := hA.jets.bound n
  exact ExpGrowth.of_bound (mul_nonneg (abs_nonneg c) hC) (fun x ↦ by
    rw [spatialJet,abs_mul];exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg c))

lemma SmoothTerminal.spatialJet_parity {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (heven:∀ x,A (-x)=A x) (c:ℝ) :
    (∀ x,spatialJet c A 0 (-x)= -spatialJet c A 0 x) ∧
    (∀ x,spatialJet c A 1 (-x)= spatialJet c A 1 x) ∧
    (∀ x,spatialJet c A 2 (-x)= -spatialJet c A 2 x) ∧
    (∀ x,spatialJet c A 3 (-x)= spatialJet c A 3 x) := by
  have h0:∀ x,spatialJet c A 0 (-x)= -spatialJet c A 0 x := by
    intro x
    have hd:∀ y,HasDerivAt A (deriv A y) y := fun y ↦
      ((hA.smooth.differentiable (by simp)) y).hasDerivAt
    have hp := derivative_parity hd (e:=1) (by simpa using heven) x
    simpa only [spatialJet,iteratedDeriv_zero,neg_one_mul,mul_neg] using congrArg (fun v ↦ c*v) hp
  have h1:∀ x,spatialJet c A 1 (-x)=spatialJet c A 1 x := by
    intro x
    simpa using derivative_parity (hA.spatialJet_space c 0) (e:= -1) (by simpa using h0) x
  have h2:∀ x,spatialJet c A 2 (-x)= -spatialJet c A 2 x := by
    intro x
    simpa using derivative_parity (hA.spatialJet_space c 1) (e:=1) (by simpa using h1) x
  have h3:∀ x,spatialJet c A 3 (-x)=spatialJet c A 3 x := by
    intro x
    simpa using derivative_parity (hA.spatialJet_space c 2) (e:= -1) (by simpa using h2) x
  exact ⟨h0,h1,h2,h3⟩

namespace ForwardDensityData
lemma jet_parity (D:ForwardDensityData) :
    (∀ x,D.jet 0 (-x)= -D.jet 0 x) ∧ (∀ x,D.jet 1 (-x)=D.jet 1 x) ∧
    (∀ x,D.jet 2 (-x)= -D.jet 2 x) := by
  obtain ⟨h0,h1,h2,h3⟩:=D.smooth.spatialJet_parity D.even D.size
  constructor
  · intro x
    change -x/D.variance-spatialJet D.size D.potential 0 (-x)=
      -(x/D.variance-spatialJet D.size D.potential 0 x)
    rw [h0];ring
  constructor
  · intro x
    change 1/D.variance-spatialJet D.size D.potential 1 (-x)=
      1/D.variance-spatialJet D.size D.potential 1 x
    rw [h1]
  · intro x
    simpa only [jet,show (2:ℕ)≠0 from by norm_num,show (2:ℕ)≠1 from by norm_num,
      ite_false,zero_sub,spatialJet] using congrArg Neg.neg (h2 x)
lemma jet_growth (D:ForwardDensityData) (n:ℕ) : ExpGrowth (D.jet n) := by
  have he:ExpGrowth (fun x:ℝ ↦ x/D.variance) := by
    have hx:ExpGrowth (fun x:ℝ ↦ x) := ⟨1,1,by norm_num,by norm_num,fun x ↦ by
      simp only [one_mul];exact (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans (Real.add_one_le_exp |x|)⟩
    simpa only [div_eq_mul_inv] using hx.mul (ExpGrowth.const D.variance⁻¹)
  by_cases h0:n=0
  · subst n;exact he.sub (D.smooth.spatialJet_growth D.size 0)
  by_cases h1:n=1
  · subst n
    exact (ExpGrowth.const (1/D.variance)).sub (D.smooth.spatialJet_growth D.size 1)
  · change ExpGrowth (fun x ↦ (if n=0 then x/D.variance else if n=1 then 1/D.variance else 0)-
      D.size*iteratedDeriv n (deriv D.potential) x)
    simpa only [h0,h1,ite_false,zero_sub,spatialJet] using
      (D.smooth.spatialJet_growth D.size n).neg
end ForwardDensityData
end SKValue

end

end OAI
