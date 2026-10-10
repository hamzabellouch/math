import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamel

namespace OAI

/-! # Exact whole-space restart and real linearity of the Duhamel operator -/

open MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

private theorem continuous_homogeneousKernel (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : Continuous r) :
    Continuous (fun τ => homogeneousFreeOperator a b k (t - τ) ha ha1 hk (r τ)) :=
  (continuous_homogeneousFreeOperator_uncurry a b k ha ha1 hk).comp
    ((continuous_const.sub continuous_id).prodMk hr)

/-- Splitting the integral gives restart at every real pair of times. -/
theorem homogeneousDuhamel_restart (a b k s t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r : ℝ → HomogeneousY a k) (hr : Continuous r) :
    homogeneousDuhamel a b k ha ha1 hk (s + t) r =
      homogeneousFreeOperator a b k t ha ha1 hk (homogeneousDuhamel a b k ha ha1 hk s r) +
        homogeneousDuhamel a b k ha ha1 hk t (fun u => r (s + u)) := by
  let F := fun τ => homogeneousFreeOperator a b k (s + t - τ) ha ha1 hk (r τ)
  have hc : Continuous F := continuous_homogeneousKernel a b k (s + t) ha ha1 hk r hr
  have hfirst : (∫ τ in 0..s, F τ) =
      homogeneousFreeOperator a b k t ha ha1 hk (homogeneousDuhamel a b k ha ha1 hk s r) := by
    rw [homogeneousDuhamel, ← ContinuousLinearMap.intervalIntegral_comp_comm _
      ((continuous_homogeneousKernel a b k s ha ha1 hk r hr).intervalIntegrable 0 s)]
    apply intervalIntegral.integral_congr
    intro τ _
    change homogeneousFreeOperator a b k (s + t - τ) ha ha1 hk (r τ) =
      homogeneousFreeOperator a b k t ha ha1 hk
        (homogeneousFreeOperator a b k (s - τ) ha ha1 hk (r τ))
    rw [← homogeneousFreeOperator_add]
    congr 2
    ring
  have hsecond : (∫ τ in s..s + t, F τ) =
      homogeneousDuhamel a b k ha ha1 hk t (fun u => r (s + u)) := by
    have hshift := intervalIntegral.integral_comp_add_left (a := 0) (b := t) F s
    simp only [add_zero] at hshift
    rw [← hshift, homogeneousDuhamel]
    apply intervalIntegral.integral_congr
    intro τ _
    change homogeneousFreeOperator a b k (s + t - (s + τ)) ha ha1 hk (r (s + τ)) = _
    congr 2
    ring
  rw [homogeneousDuhamel, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s (s + t)), hfirst, hsecond]

@[simp] theorem homogeneousDuhamel_zero (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    homogeneousDuhamel a b k ha ha1 hk t (fun _ => 0) = 0 := by
  simp [homogeneousDuhamel]

theorem homogeneousDuhamel_add (a b k t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (r q : ℝ → HomogeneousY a k) (hr : Continuous r) (hq : Continuous q) :
    homogeneousDuhamel a b k ha ha1 hk t (fun τ => r τ + q τ) =
      homogeneousDuhamel a b k ha ha1 hk t r + homogeneousDuhamel a b k ha ha1 hk t q := by
  simp only [homogeneousDuhamel, map_add]
  exact intervalIntegral.integral_add
    ((continuous_homogeneousKernel a b k t ha ha1 hk r hr).intervalIntegrable 0 t)
    ((continuous_homogeneousKernel a b k t ha ha1 hk q hq).intervalIntegrable 0 t)

theorem homogeneousDuhamel_real_smul (a b k t c : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (r : ℝ → HomogeneousY a k) :
    homogeneousDuhamel a b k ha ha1 hk t (fun τ => c • r τ) =
      c • homogeneousDuhamel a b k ha ha1 hk t r := by
  simp only [homogeneousDuhamel, ContinuousLinearMap.map_smul_of_tower,
    intervalIntegral.integral_smul]

end DefocusingNLS

end OAI
