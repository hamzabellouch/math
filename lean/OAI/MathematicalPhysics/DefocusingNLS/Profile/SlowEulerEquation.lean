import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowEulerDerivative
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! # Integration by parts for the confluent hypergeometric equation -/

open MeasureTheory Filter Topology

namespace DefocusingNLS

noncomputable def slowEulerPrimitive (q : ℂ) (m : ℕ) (x : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (-x * (v : ℂ)) * (v : ℂ) ^ q * (1 + (v : ℂ)) ^ ((m : ℂ) - q)

noncomputable def slowEulerBoundaryDerivative (q : ℂ) (m : ℕ) (x : ℂ) (v : ℝ) : ℂ :=
  -x * slowEulerKernel (q + 2) (m + 2) x v +
    ((m : ℂ) - x) * slowEulerKernel (q + 1) (m + 1) x v +
    q * slowEulerKernel q m x v

theorem hasDerivAt_slowEulerPrimitive (q : ℂ) (m : ℕ) (x : ℂ) {v : ℝ}
    (hv : 0 < v) :
    HasDerivAt (slowEulerPrimitive q m x) (slowEulerBoundaryDerivative q m x v) v := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hb0 : 1 + (v : ℂ) ≠ 0 := by
    have : 0 < (1 + (v : ℂ)).re := by simp; linarith
    intro h
    simp [h] at this
  have hp : (v : ℂ) ^ q = (v : ℂ) ^ (q - 1) * (v : ℂ) := by
    symm
    calc
      (v : ℂ) ^ (q - 1) * (v : ℂ) = (v : ℂ) ^ (q - 1) * (v : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = (v : ℂ) ^ (q - 1 + 1) := (Complex.cpow_add _ _ hv0).symm
      _ = (v : ℂ) ^ q := by congr 1; ring
  have hp' : (v : ℂ) ^ (q + 1) = (v : ℂ) ^ q * (v : ℂ) := by
    rw [Complex.cpow_add _ _ hv0, Complex.cpow_one]
  have hb : (1 + (v : ℂ)) ^ ((m : ℂ) - q) =
      (1 + (v : ℂ)) ^ ((m : ℂ) - 1 - q) * (1 + (v : ℂ)) := by
    calc
      _ = (1 + (v : ℂ)) ^ (((m : ℂ) - 1 - q) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hb0, Complex.cpow_one]
  have he := (((hasDerivAt_id (v : ℂ)).const_mul (-x)).cexp)
  have hq := (hasDerivAt_id (v : ℂ)).cpow_const (c := q)
    (Complex.ofReal_mem_slitPlane.mpr hv)
  have hm := ((hasDerivAt_id (v : ℂ)).const_add 1).cpow_const (c := (m : ℂ) - q)
    (by apply Complex.mem_slitPlane_iff.mpr; left; simp; linarith)
  have hh := ((he.mul hq).mul hm).comp_ofReal
  have hdegree : ((m + 2 : ℕ) : ℂ) - 1 - (q + 2) = (m : ℂ) - 1 - q := by
    push_cast
    ring
  have hdegree' : ((m + 1 : ℕ) : ℂ) - 1 - (q + 1) = (m : ℂ) - 1 - q := by
    push_cast
    ring
  have hqdegree : q + 2 - 1 = q + 1 := by ring
  convert! hh using 1
  simp only [slowEulerBoundaryDerivative, slowEulerKernel, hdegree, hdegree',
    add_sub_cancel_right, hqdegree, id_eq, Pi.mul_apply, mul_one]
  have heq : (m : ℂ) - q - 1 = (m : ℂ) - 1 - q := by ring
  rw [heq, hb, hp', hp]
  ring

theorem slowEulerPrimitive_eq_kernel (q : ℂ) (m : ℕ) (x : ℂ) :
    slowEulerPrimitive q m x = slowEulerKernel (q + 1) (m + 2) x := by
  funext v
  have he : ((m + 2 : ℕ) : ℂ) - 1 - (q + 1) = (m : ℂ) - q := by push_cast; ring
  simp only [slowEulerPrimitive, slowEulerKernel, add_sub_cancel_right, he]

theorem integrable_slowEulerBoundaryDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    IntegrableOn (slowEulerBoundaryDerivative q m x) (Set.Ioi 0) := by
  have hq₁ : 0 < (q + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hq₂ : 0 < (q + 2).re := by change 0 < q.re + 2; linarith
  exact (((integrable_slowEulerKernel (q + 2) (m + 2) x hq₂ hx).const_mul (-x)).add
    ((integrable_slowEulerKernel (q + 1) (m + 1) x hq₁ hx).const_mul ((m : ℂ) - x))).add
      ((integrable_slowEulerKernel q m x hq hx).const_mul q)

theorem integral_slowEulerBoundaryDerivative (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    (∫ v : ℝ in Set.Ioi 0, slowEulerBoundaryDerivative q m x v) = 0 := by
  have hi := integrable_slowEulerBoundaryDerivative q m x hq hx
  have hp : IntegrableOn (slowEulerPrimitive q m x) (Set.Ioi 0) := by
    rw [slowEulerPrimitive_eq_kernel]
    apply integrable_slowEulerKernel _ _ _ _ hx
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hd := fun v (hv : v ∈ Set.Ioi (0 : ℝ)) => hasDerivAt_slowEulerPrimitive q m x hv
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hd hi hp
  have hc : ContinuousAt (slowEulerPrimitive q m x) 0 := by
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · fun_prop
      · exact Complex.continuousAt_ofReal_cpow_const 0 q (Or.inl hq)
    · exact (show ContinuousAt (fun v : ℝ => 1 + (v : ℂ)) 0 by fun_prop).cpow
        continuousAt_const (by simp)
  have hz : slowEulerPrimitive q m x 0 = 0 := by
    have hq0 : q ≠ 0 := by intro h; simp [h] at hq
    simp [slowEulerPrimitive, hq0]
  simpa only [hz, sub_zero] using
    integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt hd hi hlim

/-- The integral identity underlying Kummer's equation. -/
theorem slowEuler_integral_relation (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : 0 < q.re) (hx : 0 < x.re) :
    x * (∫ v : ℝ in Set.Ioi 0, slowEulerKernel (q + 2) (m + 2) x v) +
      (x - (m : ℂ)) * (∫ v : ℝ in Set.Ioi 0, slowEulerKernel (q + 1) (m + 1) x v) -
      q * (∫ v : ℝ in Set.Ioi 0, slowEulerKernel q m x v) = 0 := by
  have hq₁ : 0 < (q + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hq₂ : 0 < (q + 2).re := by change 0 < q.re + 2; linarith
  have h₀ := integrable_slowEulerKernel q m x hq hx
  have h₁ := integrable_slowEulerKernel (q + 1) (m + 1) x hq₁ hx
  have h₂ := integrable_slowEulerKernel (q + 2) (m + 2) x hq₂ hx
  have h := integral_slowEulerBoundaryDerivative q m x hq hx
  unfold slowEulerBoundaryDerivative at h
  rw [integral_add
      (f := fun v => -x * slowEulerKernel (q + 2) (m + 2) x v +
        ((m : ℂ) - x) * slowEulerKernel (q + 1) (m + 1) x v)
      (g := fun v => q * slowEulerKernel q m x v)
      ((h₂.const_mul (-x)).add (h₁.const_mul ((m : ℂ) - x))) (h₀.const_mul q),
    integral_add (h₂.const_mul (-x)) (h₁.const_mul ((m : ℂ) - x))] at h
  simp only [integral_const_mul] at h
  linear_combination -h

end DefocusingNLS

end OAI
