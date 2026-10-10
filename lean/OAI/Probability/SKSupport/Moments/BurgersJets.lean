import Mathlib
import OAI.Probability.SKSupport.Parabolic.BurgersConstruction

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma jet_spatial (n : ℕ) (t x : ℝ) :
    HasDerivAt (iteratedDeriv n (r t)) (iteratedDeriv (n+1) (r t) x) x :=
  hasDerivAt_spatialJet (hr.family.regular t).smooth n x

lemma jet_continuous (n : ℕ) (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => iteratedDeriv n (r p.1) p.2) (Icc (0:ℝ) T ×ˢ univ) :=
  hr.family.continuousOn_iteratedDeriv (hr.continuous T) n

lemma rate_family : BoundedSmoothFamily (burgersRate r) := by
  convert (hr.family.deriv.deriv.const_mul (1/2:ℝ)).add (hr.family.mul hr.family.deriv) using 1
  funext t x
  simp only [burgersRate,iteratedDeriv_succ,iteratedDeriv_zero]

lemma rate_continuous (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => burgersRate r p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  exact (continuousOn_const.mul (hr.jet_continuous 2 T)).add
    ((hr.continuous T).mul (by simpa only [iteratedDeriv_one] using hr.jet_continuous 1 T))

lemma rate_deriv (t x : ℝ) :
    deriv (burgersRate r t) x = (1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x := by
  have hd := ((hr.jet_spatial 2 t x).const_mul (1/2:ℝ)).add
    ((hr.jet_spatial 0 t x).mul (hr.jet_spatial 1 t x))
  have hd' : HasDerivAt (burgersRate r t) ((1/2:ℝ)*iteratedDeriv 3 (r t) x+
      (deriv (r t) x)^2+r t x*iteratedDeriv 2 (r t) x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only
      [burgersRate,Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma rate_jet2 (t x : ℝ) :
    iteratedDeriv 2 (burgersRate r t) x = (1/2:ℝ)*iteratedDeriv 4 (r t) x+
      3*deriv (r t) x*iteratedDeriv 2 (r t) x+r t x*iteratedDeriv 3 (r t) x := by
  have he : deriv (burgersRate r t) = fun y => (1/2:ℝ)*iteratedDeriv 3 (r t) y+
      (deriv (r t) y)^2+r t y*iteratedDeriv 2 (r t) y := funext (hr.rate_deriv t)
  have hd := (((hr.jet_spatial 3 t x).const_mul (1/2:ℝ)).add
    ((hr.jet_spatial 1 t x).pow 2)).add ((hr.jet_spatial 0 t x).mul (hr.jet_spatial 2 t x))
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  convert hd.deriv using 1 <;> first | rfl | (simp only [iteratedDeriv_succ,iteratedDeriv_zero]; first | rfl | ring)

lemma rate_jet3 (t x : ℝ) :
    iteratedDeriv 3 (burgersRate r t) x = (1/2:ℝ)*iteratedDeriv 5 (r t) x+
      3*(iteratedDeriv 2 (r t) x)^2+4*deriv (r t) x*iteratedDeriv 3 (r t) x+
      r t x*iteratedDeriv 4 (r t) x := by
  have he : iteratedDeriv 2 (burgersRate r t) = fun y => (1/2:ℝ)*iteratedDeriv 4 (r t) y+
      3*deriv (r t) y*iteratedDeriv 2 (r t) y+r t y*iteratedDeriv 3 (r t) y := funext (hr.rate_jet2 t)
  have hd := (((hr.jet_spatial 4 t x).const_mul (1/2:ℝ)).add
    (((hr.jet_spatial 1 t x).const_mul 3).mul (hr.jet_spatial 2 t x))).add
    ((hr.jet_spatial 0 t x).mul (hr.jet_spatial 3 t x))
  rw [iteratedDeriv_succ (n := 2),he]
  convert hd.deriv using 1 <;> first | rfl | (simp only [iteratedDeriv_succ,iteratedDeriv_zero]; first | rfl | ring)

lemma rate_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => burgersRate r s x)
      ((1/2:ℝ)*iteratedDeriv 2 (burgersRate r t) x+
        r t x*deriv (burgersRate r t) x+deriv (r t) x*burgersRate r t x) t := by
  convert ((hr.time_derivative 2 t ht x).const_mul (1/2:ℝ)).add
    ((hr.time_derivative 0 t ht x).mul (hr.time_derivative 1 t ht x)) using 1 <;>
    first | rfl | ((try funext y); simp only [burgersRate,Pi.add_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma rate_deriv_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => deriv (burgersRate r s) x)
      ((1/2:ℝ)*iteratedDeriv 3 (burgersRate r t) x+
        2*deriv (r t) x*deriv (burgersRate r t) x+
        burgersRate r t x*iteratedDeriv 2 (r t) x+
        r t x*iteratedDeriv 2 (burgersRate r t) x) t := by
  have he : (fun s => deriv (burgersRate r s) x) = fun s =>
      (1/2:ℝ)*iteratedDeriv 3 (r s) x+(deriv (r s) x)^2+r s x*iteratedDeriv 2 (r s) x :=
    funext (fun s => hr.rate_deriv s x)
  rw [he]
  convert (((hr.time_derivative 3 t ht x).const_mul (1/2:ℝ)).add
    ((hr.time_derivative 1 t ht x).pow 2)).add
    ((hr.time_derivative 0 t ht x).mul (hr.time_derivative 2 t ht x)) using 1 <;>
    first | rfl | ((try funext y); simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)

lemma rate_odd (ho : ∀ t, Function.Odd (r t)) (t : ℝ) : Function.Odd (burgersRate r t) := by
  have he := odd_deriv_even ((hr.family.regular t).smooth.differentiable (by simp)) (ho t)
  have hw := even_deriv_odd ((hr.family.deriv.regular t).smooth.differentiable (by simp)) he
  intro x
  simp only [burgersRate,iteratedDeriv_succ,iteratedDeriv_zero,hw x,he x,ho t x]
  ring

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def backwardWronskian (r : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  r t x*deriv (burgersRate r t) x-deriv (r t) x*burgersRate r t x

def wronskianRate (r : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  burgersRate r t x*deriv (burgersRate r t) x+
    r t x*((1/2:ℝ)*iteratedDeriv 3 (burgersRate r t) x+
      2*deriv (r t) x*deriv (burgersRate r t) x+
      burgersRate r t x*iteratedDeriv 2 (r t) x+
      r t x*iteratedDeriv 2 (burgersRate r t) x)-
    (deriv (burgersRate r t) x*burgersRate r t x+
      deriv (r t) x*((1/2:ℝ)*iteratedDeriv 2 (burgersRate r t) x+
        r t x*deriv (burgersRate r t) x+deriv (r t) x*burgersRate r t x))

namespace SmoothBurgers
variable {r : ℝ → ℝ → ℝ} (hr : SmoothBurgers r)
include hr

lemma wronskian_family : BoundedSmoothFamily (backwardWronskian r) := by
  convert (hr.family.mul hr.rate_family.deriv).add
    ((hr.family.deriv.mul hr.rate_family).const_mul (-1)) using 1
  funext t x
  simp only [backwardWronskian]
  ring

lemma wronskian_continuous (T : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => backwardWronskian r p.1 p.2) (Icc (0:ℝ) T ×ˢ univ) := by
  apply ContinuousOn.sub
  · exact (hr.continuous T).mul (by simpa only [iteratedDeriv_one] using
      hr.rate_family.continuousOn_iteratedDeriv (hr.rate_continuous T) 1)
  · have hv : ContinuousOn (fun p : ℝ × ℝ => deriv (r p.1) p.2) (Icc (0:ℝ) T ×ˢ univ) := by
      simpa only [iteratedDeriv_one] using hr.jet_continuous 1 T
    exact hv.mul (hr.rate_continuous T)

lemma wronskian_deriv (t x : ℝ) :
    deriv (backwardWronskian r t) x =
      r t x*iteratedDeriv 2 (burgersRate r t) x-iteratedDeriv 2 (r t) x*burgersRate r t x := by
  have hp (n) := hasDerivAt_spatialJet (hr.rate_family.regular t).smooth n x
  have hd := ((hr.jet_spatial 0 t x).mul (hp 1)).sub ((hr.jet_spatial 1 t x).mul (hp 0))
  have hd' : HasDerivAt (backwardWronskian r t)
      (r t x*iteratedDeriv 2 (burgersRate r t) x-iteratedDeriv 2 (r t) x*burgersRate r t x) x := by
    convert hd using 1 <;> first | rfl | ((try funext y); simp only
      [backwardWronskian,Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero] <;> ring)
  exact hd'.deriv

lemma wronskian_jet2 (t x : ℝ) :
    iteratedDeriv 2 (backwardWronskian r t) x =
      deriv (r t) x*iteratedDeriv 2 (burgersRate r t) x+
      r t x*iteratedDeriv 3 (burgersRate r t) x-
      (iteratedDeriv 3 (r t) x*burgersRate r t x+
        iteratedDeriv 2 (r t) x*deriv (burgersRate r t) x) := by
  have hp (n) := hasDerivAt_spatialJet (hr.rate_family.regular t).smooth n x
  have he : deriv (backwardWronskian r t) = fun y =>
      r t y*iteratedDeriv 2 (burgersRate r t) y-iteratedDeriv 2 (r t) y*burgersRate r t y :=
    funext (hr.wronskian_deriv t)
  rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one,he]
  convert (((hr.jet_spatial 0 t x).mul (hp 2)).sub ((hr.jet_spatial 2 t x).mul (hp 0))).deriv
    using 1 <;> first | rfl | simp only [iteratedDeriv_succ,iteratedDeriv_zero]

lemma wronskian_time {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun s => backwardWronskian r s x) (wronskianRate r t x) t := by
  convert ((hr.time_derivative 0 t ht x).mul (hr.rate_deriv_time ht x)).sub
    ((hr.time_derivative 1 t ht x).mul (hr.rate_time ht x)) using 1 <;>
    first | rfl | ((try funext y); simp only [backwardWronskian,wronskianRate,
      Pi.sub_apply,Pi.mul_apply,iteratedDeriv_succ,iteratedDeriv_zero])

lemma wronskian_equation (t x : ℝ) (hne : r t x ≠ 0) :
    wronskianRate r t x-(1/2:ℝ)*iteratedDeriv 2 (backwardWronskian r t) x-
      (r t x-deriv (r t) x/r t x)*deriv (backwardWronskian r t) x-
      2*(burgersRate r t x/r t x)*backwardWronskian r t x =
        r t x*iteratedDeriv 2 (r t) x*burgersRate r t x := by
  rw [hr.wronskian_jet2,hr.wronskian_deriv]
  simp only [wronskianRate,backwardWronskian,hr.rate_deriv,hr.rate_jet2,hr.rate_jet3,burgersRate]
  field_simp [hne]
  ring

lemma wronskian_odd (ho : ∀ t, Function.Odd (r t)) (t : ℝ) :
    Function.Odd (backwardWronskian r t) := by
  have hr' := odd_deriv_even ((hr.family.regular t).smooth.differentiable (by simp)) (ho t)
  have hp := hr.rate_odd ho t
  have hp' := odd_deriv_even ((hr.rate_family.regular t).smooth.differentiable (by simp)) hp
  intro x
  simp only [backwardWronskian,ho t x,hr' x,hp x,hp' x]
  ring

end SmoothBurgers
end ZeroTemperatureSK.Heat

end
end

end OAI
