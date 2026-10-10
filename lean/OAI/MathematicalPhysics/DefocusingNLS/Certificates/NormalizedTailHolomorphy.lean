import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowLaguerreHolomorphy
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.AnalyticMatchingColumn

namespace OAI

/-! # Holomorphy of the normalized tail and its disk-valued ratio -/

open Set Polynomial

namespace DefocusingNLS

theorem differentiableAt_slowLaguerreB (q : ℂ) (m n : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => slowLaguerreB z m s n) q := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (fun h => hsim (by simp [h]))
  have hb := differentiableAt_regularizedSlowSolution_parameter_closed q m (-s) hq
    (by simp [hsre]) hs0
  have hsum : DifferentiableAt ℂ
      (fun z => ∑ j ∈ Finset.range n, slowLaguerreCoefficient z m s j) q :=
    DifferentiableAt.fun_sum fun j _ => differentiableAt_slowLaguerreCoefficient q m j s hq hsre hsim
  convert! hb.sub hsum using 1
  funext z
  simp [slowLaguerreB, shiftedSlowDerivative]

theorem differentiableAt_normalizedSlowB (q : ℂ) (m n : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => normalizedSlowB z m s n) q := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  have h : DifferentiableAt ℂ (fun z => slowLaguerreCoefficient z (m + 1) s (n - 1)) (q + 1) :=
    differentiableAt_slowLaguerreCoefficient (q + 1) (m + 1) (n - 1) s hq' hsre hsim
  have hs : DifferentiableAt ℂ (fun z : ℂ => z + 1) q := differentiableAt_id.add_const 1
  convert! h.comp q hs using 1

theorem differentiableAt_normalizedSlowC (q : ℂ) (m n : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => normalizedSlowC z m s n) q := by
  have hq' : -1 < (q + 1).re := by change -1 < q.re + 1; linarith
  exact (differentiableAt_slowLaguerreB (q + 1) (m + 1) n s hq' hsre hsim).comp q
    (differentiableAt_id.add_const 1)

theorem differentiableAt_normalizedMatchingB (q : ℂ) (m K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => normalizedMatchingB z m s K) q := by
  have hp := ((ascPochhammer ℂ (K - 1)).hasDerivAt (q + 1)).differentiableAt.comp q
    (differentiableAt_id.add_const 1)
  exact (differentiableAt_normalizedSlowB q m K s hq hsre hsim).div hp
    (shiftedPochhammer_ne_zero q (K - 1) hq)

theorem differentiableAt_normalizedMatchingC (q : ℂ) (m K : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => normalizedMatchingC z m s K) q := by
  have hp := ((ascPochhammer ℂ (K - 1)).hasDerivAt (q + 1)).differentiableAt.comp q
    (differentiableAt_id.add_const 1)
  exact (differentiableAt_normalizedSlowC q m K s hq hsre hsim).div hp
    (shiftedPochhammer_ne_zero q (K - 1) hq)

theorem analyticOnNhd_normalizedMatchingB (m K : ℕ) (s : ℂ)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AnalyticOnNhd ℂ (fun q => normalizedMatchingB q m s K) {q : ℂ | -1 < q.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro q hq
  exact (differentiableAt_normalizedMatchingB q m K s hq hsre hsim).differentiableWithinAt

theorem analyticOnNhd_normalizedMatchingC (m K : ℕ) (s : ℂ)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AnalyticOnNhd ℂ (fun q => normalizedMatchingC q m s K) {q : ℂ | -1 < q.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro q hq
  exact (differentiableAt_normalizedMatchingC q m K s hq hsre hsim).differentiableWithinAt

noncomputable def slowTailRatio (q : ℂ) (m K : ℕ) (s : ℂ) : ℂ :=
  normalizedMatchingB q m s K / normalizedMatchingC q m s K

/-- Holomorphy includes the boundary of the counting half-plane and q=0. -/
theorem analyticAt_slowTailRatio (q : ℂ) (ℓ K : ℕ) (s : ℂ)
    (hK : 3 ≤ K) (hq : -(1 / 32 : ℝ) ≤ q.re - (ℓ : ℝ) / 2)
    (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    AnalyticAt ℂ (fun z => slowTailRatio z (ℓ + 6) K s) q := by
  have hq' : -1 < q.re := by linarith [Nat.cast_nonneg (α := ℝ) ℓ]
  have hC := (normalizedMatching_tail_disk (q.re - (ℓ : ℝ) / 2) ℓ K q s hq hK
    (by ring) hsre hsim).1
  exact ((analyticOnNhd_normalizedMatchingB (ℓ + 6) K s hsre hsim) q hq').div
    ((analyticOnNhd_normalizedMatchingC (ℓ + 6) K s hsre hsim) q hq') hC

end DefocusingNLS

end OAI
