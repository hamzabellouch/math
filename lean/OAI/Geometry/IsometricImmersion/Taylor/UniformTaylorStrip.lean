import OAI.Geometry.IsometricImmersion.Taylor.TaylorRemainderBound

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def taylorStripJetOrder (N : ℕ) : ℕ := max 3 (N + 2)

theorem uniform_taylor_strip
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ epsilon R C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 ≤ R ∧ 0 ≤ C ∧
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ) (a : ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, a] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy a u0 u1) ![x, a]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy a u0 u1) ![x, a] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      ∀ b : ℝ, a ≤ b → b - a ≤ epsilon →
      (∀ x ∈ J, ∀ t ∈ Icc a b, (![x, t] : Coord) ∈ S) →
      let z0 := taylorApproximation g a u0 u1 N
      (∀ x ∈ J, ∀ t ∈ Icc a b, ∀ j ≤ taylorStripJetOrder N,
        ‖iteratedFDeriv ℝ j z0 ![x, t]‖ ≤ R) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b, c / 2 ≤ |covHessian g z0 ![x, t] 0 0|) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b,
        |iteratedDeriv N (fun s => qResidual g z0 ![x, s]) t| ≤ C) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b, |qResidual g z0 ![x, t]| ≤ C * (t - a)^N) := by
  obtain ⟨R, hR, hpoly⟩ := uniform_taylorApproximation_jets hg hU hS hSU M hM hc B hB
    N (taylorStripJetOrder N)
  obtain ⟨epsilon, he, he1, hwidth⟩ := exists_uniform_Hxx_strip_width hg hU hS hSU R hR hc
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun p : Coord => p) S)
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hpoint : ∀ p ∈ S, ‖p‖ ≤ A0 := fun p hp => (hA p hp).trans (le_max_left _ _)
  obtain ⟨C0, hC0, hresidual⟩ := exists_uniform_qResidual_fullJet_bound hg hU hS hSU
    (max A0 R) (hA0.trans (le_max_left _ _)) (half_pos hc) N
  let C := R + (N.factorial : ℝ) * C0 * (max 1 R)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨epsilon, R, C, he, he1, hR, hC, ?_⟩
  intro u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B b hab hba hstrip
  dsimp only
  have hxx0 : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0 := by
    intro x hx hh
    have hd := hden x hx
    rw [hh, abs_zero] at hd
    linarith
  obtain ⟨hP, hjet, hzero⟩ := taylorApproximation_properties hg hU hI h0 h1 a
    (fun x hx => hSU (hcut x hx)) hxx0 N
  have hfull := hpoly u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B
  have htime (t : ℝ) (ht : t ∈ Icc a b) : |t - a| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact (sub_le_sub_right ht.2 a).trans (hba.trans he1)
  have hfull' : ∀ x ∈ J, ∀ t ∈ Icc a b, ∀ j ≤ taylorStripJetOrder N,
      ‖iteratedFDeriv ℝ j (taylorApproximation g a u0 u1 N) ![x, t]‖ ≤ R := by
    intro x hx t ht j hj
    exact hfull j hj ![x, t] hx (htime t ht)
  have hden0 : ∀ x ∈ I,
      c ≤ |covHessian g (taylorApproximation g a u0 u1 N) ![x, a] 0 0| := by
    intro x hx
    rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
    exact hden x hx
  have hdenAll : ∀ x ∈ J, ∀ t ∈ Icc a b,
      c / 2 ≤ |covHessian g (taylorApproximation g a u0 u1 N) ![x, t] 0 0| := by
    intro x hx t ht
    apply hwidth (taylorApproximation g a u0 u1 N) I hI hP a t x ht.1
      ((sub_le_sub_right ht.2 a).trans hba) (hJI hx)
    · intro s hs
      exact hstrip x hx s ⟨hs.1, hs.2.trans ht.2⟩
    · intro s hs j hj
      exact hfull' x hx s ⟨hs.1, hs.2.trans ht.2⟩ j
        (hj.trans (le_max_left _ _))
    · exact hden0 x (hJI hx)
  have hne : ∀ x ∈ J, ∀ t ∈ Icc a b,
      covHessian g (taylorApproximation g a u0 u1 N) ![x, t] 0 0 ≠ 0 := by
    intro x hx t ht hh
    have hd := hdenAll x hx t ht
    rw [hh, abs_zero] at hd
    linarith
  have hstateAll : ∀ x ∈ J, ∀ t ∈ Icc a b,
      ‖qSolutionJet (taylorApproximation g a u0 u1 N) ![x, t]‖ ≤ max A0 R := by
    intro x hx t ht
    apply qSolutionJet_norm_bound hP (spatialStrip_isOpen hI) (hJI hx) hA0 hR
      (hpoint _ (hstrip x hx t ht))
    intro j hj
    exact hfull' x hx t ht j (hj.trans (by unfold taylorStripJetOrder; omega))
  have hresBound : ∀ x ∈ J, ∀ t ∈ Icc a b,
      ‖iteratedFDeriv ℝ N (qResidual g (taylorApproximation g a u0 u1 N)) ![x, t]‖ ≤ C := by
    intro x hx t ht
    exact hresidual (taylorApproximation g a u0 u1 N) I hI hP ![x, t] (hJI hx)
      (hstrip x hx t ht) (hstateAll x hx t ht) (hdenAll x hx t ht) N le_rfl R
      (fun j hj => hfull' x hx t ht j (hj.trans (le_max_right _ _)))
  have htimeBound : ∀ x ∈ J, ∀ t ∈ Icc a b,
      |iteratedDeriv N (fun s => qResidual g (taylorApproximation g a u0 u1 N) ![x, s]) t| ≤ C := by
    intro x hx t ht
    exact (qResidual_time_jet_le_fullJet hg hU hI hP x t (hJI hx)
      (hSU (hstrip x hx t ht)) (hne x hx t ht) N).trans (hresBound x hx t ht)
  refine ⟨hfull', hdenAll, htimeBound, ?_⟩
  intro x hx t ht
  apply zero_jets_remainder_bound hab ?_ N (hzero x (hJI hx)) hC
    (htimeBound x hx) ht
  intro s hs
  exact ((qResidual_contDiffOn hg hU hI hP).contDiffAt
    ((comparisonDomain_isOpen hg hU hI hP).mem_nhds
      (mem_comparisonDomain (hJI hx) (hSU (hstrip x hx s hs)) (hne x hx s hs)))).comp s
        (verticalPoint_contDiff x).contDiffAt

end SmoothLocal.Taylor

end

end OAI
