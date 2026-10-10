import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleFiniteFactor

namespace OAI

/-! # The rectangular contour integral counts the finite analytic divisor -/

open Set Function MeromorphicOn
namespace DefocusingNLS

theorem countingBoundaryIntegral_sum {ι : Type*} (V : ℝ) (hV : 0 < V)
    (s : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ s, ContinuousOn (F i) (countingRectangleBoundary V)) :
    countingBoundaryIntegral V (fun z => ∑ i ∈ s, F i z) =
      ∑ i ∈ s, countingBoundaryIntegral V (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hF
      simp only [Finset.sum_insert ha]
      rw [countingBoundaryIntegral_add V hV _ _ hF.1 (continuousOn_finsetSum s hF.2), ih hF.2]

theorem countingBoundaryIntegral_eq_degree (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    countingBoundaryIntegral V (logDeriv f) =
      (countingZeroDegree V f : ℂ) * countingBoundaryIntegral V (fun z => z⁻¹) := by
  classical
  obtain ⟨g, hg, hgn, he⟩ := rectangle_finite_factorization V hV f hf hn
  have hp : AnalyticOnNhd ℂ (countingDivisorFactor V f) (closedCountingRectangle V) :=
    (countingDivisorFactor_analytic V f).mono (subset_univ _)
  have hm := hp.mul hg
  have hd := rectangle_eqOn_deriv V hV f _ hf hm he
  have hlog : EqOn (logDeriv f)
      (fun z => logDeriv (countingDivisorFactor V f) z + logDeriv g z)
      (countingRectangleBoundary V) := by
    intro z hz
    calc
      logDeriv f z = logDeriv (fun w => countingDivisorFactor V f w * g w) z := by
        simp only [logDeriv_apply, hd hz.1, he hz.1]
      _ = _ := logDeriv_fun_mul z (countingDivisorFactor_ne_zero V f hf hn z hz)
        (hgn z hz.1) (hp z hz.1).differentiableAt (hg z hz.1).differentiableAt
  have hpc : ContinuousOn (logDeriv (countingDivisorFactor V f)) (countingRectangleBoundary V) :=
    ((hp.mono fun _ hz => hz.1).deriv.div (hp.mono fun _ hz => hz.1)
      (countingDivisorFactor_ne_zero V f hf hn)).continuousOn
  have hgc : ContinuousOn (logDeriv g) (countingRectangleBoundary V) :=
    ((hg.deriv.div hg hgn).mono fun _ hz => hz.1).continuousOn
  have hgzero : countingBoundaryIntegral V (logDeriv g) = 0 := by
    change countingBoundaryIntegral V (fun z => deriv g z / g z) = 0
    exact countingBoundaryIntegral_eq_zero V hV _ (hg.deriv.div hg hgn)
  rw [countingBoundaryIntegral_congr V hV hlog,
    countingBoundaryIntegral_add V hV _ _ hpc hgc,
    hgzero, add_zero]
  rw [countingBoundaryIntegral_congr V hV (fun z hz => countingDivisorFactor_logDeriv V f hf hn z hz)]
  have hcont (a : ℂ) (ha : a ∈ countingDivisorPoints V f) :
      ContinuousOn (fun z : ℂ => ((divisor f (closedCountingRectangle V) a).toNat : ℂ) * (z - a)⁻¹)
        (countingRectangleBoundary V) := by
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ (by fun_prop)
    intro z hz
    exact sub_ne_zero.mpr (countingBoundary_ne_interior hz (countingDivisorPoints_subset V f hf hn a ha))
  rw [countingBoundaryIntegral_sum V hV _ _ hcont]
  calc
    _ = ∑ a ∈ countingDivisorPoints V f, ((divisor f (closedCountingRectangle V) a).toNat : ℂ) *
        countingBoundaryIntegral V (fun z => z⁻¹) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [countingBoundaryIntegral_const_mul]
      congr 1
      simpa only [sub_zero] using countingBoundaryIntegral_inv_sub_eq V hV a 0
        (countingDivisorPoints_subset V f hf hn a ha) (zero_mem_countingRectangle V hV)
    _ = _ := by rw [← Finset.sum_mul, countingZeroDegree, Nat.cast_sum]

end DefocusingNLS

end OAI
