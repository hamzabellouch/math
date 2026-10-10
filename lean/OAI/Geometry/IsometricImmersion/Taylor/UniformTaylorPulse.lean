import OAI.Geometry.IsometricImmersion.Taylor.UniformTaylorStrip

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_pulse_width_threshold {epsilon delta : ℝ} (he : 0 < epsilon)
    (_hd : 0 < delta) :
    ∃ tau0 : ℕ, 0 < tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      0 < tau ∧ 2 * delta / (tau : ℝ) ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * delta / epsilon)
  refine ⟨max 1 n, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  intro tau htau
  have ht : 0 < tau := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans htau)
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr ht
  have hnreal : (n : ℝ) ≤ (tau : ℝ) := by exact_mod_cast (le_max_right 1 n).trans htau
  have hn' : 2 * delta < (n : ℝ) * epsilon := (div_lt_iff₀ he).mp hn
  refine ⟨ht, (div_le_iff₀ htr).mpr ?_⟩
  nlinarith

theorem pulse_time_power_bound {delta C t : ℝ} {tau N : ℕ}
    (_hd : 0 < delta) (hdhalf : delta ≤ 1 / 2) (htau : 0 < tau) (hC : 0 ≤ C)
    (ht : t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ))) :
    C * (t - (-delta / (tau : ℝ)))^N ≤ C / (tau : ℝ)^N := by
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr htau
  have hleft : 0 ≤ t - (-delta / (tau : ℝ)) := sub_nonneg.mpr ht.1
  have hright : t - (-delta / (tau : ℝ)) ≤ 1 / (tau : ℝ) := by
    have hw : t - (-delta / (tau : ℝ)) ≤ 2 * delta / (tau : ℝ) := by
      have hs := sub_le_sub_right ht.2 (-delta / (tau : ℝ))
      convert hs using 1; first | rfl | ring
    exact hw.trans ((div_le_div_iff_of_pos_right htr).mpr (by linarith))
  have hp := pow_le_pow_left₀ hleft hright N
  have hm := mul_le_mul_of_nonneg_left hp hC
  simpa only [div_pow, one_pow, mul_one_div] using hm

theorem uniform_taylor_pulse
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 2 →
      ∃ tau0 : ℕ, 0 < tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, -delta / (tau : ℝ)] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      (∀ x ∈ J, ∀ t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ)),
        (![x, t] : Coord) ∈ S) →
      let z0 := taylorApproximation g (-delta / (tau : ℝ)) u0 u1 N
      ContDiffOn ℝ ∞ z0 (spatialStrip I) ∧
      (∀ x ∈ I, z0 ![x, -delta / (tau : ℝ)] = u0 x ∧
        coordPartial 1 z0 ![x, -delta / (tau : ℝ)] = u1 x) ∧
      (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧ ∀ t, p.eval t = z0 ![x, t]) ∧
      (∀ x ∈ J, ∀ t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ)),
        c / 2 ≤ |covHessian g z0 ![x, t] 0 0| ∧
        |qResidual g z0 ![x, t]| ≤ C / (tau : ℝ)^N) := by
  obtain ⟨epsilon, _, C, he, _, _, hC, hstrip⟩ := uniform_taylor_strip
    hg hU hS hSU M hM hc B hB N
  refine ⟨C, hC, ?_⟩
  intro delta hd hdhalf
  obtain ⟨tau0, htau0, hwidth⟩ := exists_pulse_width_threshold he hd
  refine ⟨tau0, htau0, ?_⟩
  intro tau htau u0 u1 I J hI hJI h0 h1 hcut hstate hden h0B h1B hregion
  obtain ⟨htaupos, hthin⟩ := hwidth tau htau
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr htaupos
  have hab : -delta / (tau : ℝ) ≤ delta / (tau : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) htr.le
  have hwidth' : delta / (tau : ℝ) - (-delta / (tau : ℝ)) ≤ epsilon := by
    convert hthin using 1; first | rfl | ring
  have hdata := hstrip u0 u1 I J (-delta / (tau : ℝ)) hI hJI h0 h1 hcut hstate hden
    h0B h1B (delta / (tau : ℝ)) hab hwidth' hregion
  have hxx : ∀ x ∈ I,
      covHessian g (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)] 0 0 ≠ 0 := by
    intro x hx hh
    have hd' := hden x hx
    rw [hh, abs_zero] at hd'
    linarith
  obtain ⟨hP, hinitial, hdegree, _, _⟩ := finiteTaylorComparison hg hU hI h0 h1
    (-delta / (tau : ℝ)) (fun x hx => hSU (hcut x hx)) hxx N
  refine ⟨hP, hinitial, hdegree, ?_⟩
  intro x hx t ht
  exact ⟨hdata.2.1 x hx t ht, (hdata.2.2.2 x hx t ht).trans
    (pulse_time_power_bound hd hdhalf htaupos hC ht)⟩

end SmoothLocal.Taylor

end

end OAI
