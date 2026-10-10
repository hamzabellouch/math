import OAI.Analysis.CircleDomains.Modulus.FiniteCircleLinePayment
import Mathlib.Topology.Order.Compact

namespace OAI

/-!
# Collapse from vanishing finite-circle barriers

The proved finite-hole line estimate rules out a fixed positive-length
set of crossings when both the actual gradient norms and terminal
oscillation norms vanish. This is the analytic contradiction used for
unmarked limiting complementary components.
-/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem measure_zero_of_vanishing_finite_circle_barriers
    {I : ℕ → Type*} [∀ n, Fintype (I n)]
    (c : (n : ℕ) → I n → ℂ) (r A : (n : ℕ) → I n → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hr : ∀ n i, 0 ≤ r n i) (hA : ∀ n i, 0 ≤ A n i)
    (hdisj : ∀ n, Pairwise (Disjoint on fun i => closedBall (c n i) (r n i)))
    (hsub : ∀ n i, closedBall (c n i) (r n i) ⊆ closedBall 0 L)
    (v : ℕ → ℂ → ℝ)
    (hv : ∀ n, ContDiffOn ℝ 1 (v n) (⋃ i, closedBall (c n i) (r n i))ᶜ)
    (henergy : ∀ n, IntegrableOn (euclideanGradientEnergy (v n))
      ((⋃ i, closedBall (c n i) (r n i))ᶜ ∩ closedBall 0 L))
    (hcluster : ∀ n i p q u w,
      p ∈ closedBall (c n i) (r n i) → q ∈ closedBall (c n i) (r n i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c n j) (r n j))ᶜ] p) (v n) →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c n j) (r n j))ᶜ] q) (v n) → |w - u| ≤ A n i)
    (hE : Tendsto (fun n => Real.sqrt (∫ z in
      (⋃ i, closedBall (c n i) (r n i))ᶜ ∩ closedBall 0 L,
        euclideanGradientEnergy (v n) z)) atTop (𝓝 0))
    (hosc : Tendsto (fun n => Real.sqrt (∑ i, A n i ^ 2)) atTop (𝓝 0))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ a b : ℝ, a < b ∧
      a ∈ diskLineDomain (c n) (r n) y ∧ b ∈ diskLineDomain (c n) (r n) y ∧
      horizontalLine y a ∈ closedBall 0 L ∧ horizontalLine y b ∈ closedBall 0 L ∧
      v n (horizontalLine y a) = 0 ∧ v n (horizontalLine y b) = 1) :
    volume J = 0 := by
  have hpay : ∀ᶠ n in atTop, (volume J).toReal ≤
      Real.sqrt Real.pi * L * Real.sqrt (∫ z in
        (⋃ i, closedBall (c n i) (r n i))ᶜ ∩ closedBall 0 L,
          euclideanGradientEnergy (v n) z) + 2 * L * Real.sqrt (∑ i, A n i ^ 2) := by
    filter_upwards [hcross] with n hn
    exact parallel_line_payment_on_finite_disk_complement_square_norm
      (c n) (r n) (A n) (hr n) (hA n) hL (hdisj n) (hsub n) (hv n) (henergy n)
      (hcluster n) hJ hn
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * Real.sqrt (∫ z in
      (⋃ i, closedBall (c n i) (r n i))ᶜ ∩ closedBall 0 L,
        euclideanGradientEnergy (v n) z) + 2 * L * Real.sqrt (∑ i, A n i ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds.mul hE).add (tendsto_const_nhds.mul hosc))
  have hz : (volume J).toReal = 0 := le_antisymm (ge_of_tendsto ht hpay) ENNReal.toReal_nonneg
  have hfinite : volume J ≠ ⊤ := by
    obtain ⟨n, hn⟩ := hcross.exists
    have hJsub : J ⊆ Icc (-L) L := by
      intro y hy
      obtain ⟨a, _, _, _, _, ha, _⟩ := hn y hy
      simpa only [Complex.zero_im, zero_sub, zero_add] using
        (horizontal_line_meets_closedBall (0 : ℂ)).mp ⟨a, ha⟩
    exact ne_of_lt ((measure_mono hJsub).trans_lt measure_Icc_lt_top)
  simpa only [ENNReal.toReal_eq_zero_iff, hfinite, or_false] using hz

theorem subsingleton_of_zero_projection_measure {K : Set ℂ}
    (hK : IsCompact K) (hconn : IsConnected K)
    (hre : volume (Complex.re '' K) = 0) (him : volume (Complex.im '' K) = 0) :
    K.Subsingleton := by
  have hRe : Complex.re '' K = Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    eq_Icc_of_connected_compact
      (hconn.image _ Complex.continuous_re.continuousOn) (hK.image Complex.continuous_re)
  have hIm : Complex.im '' K = Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    eq_Icc_of_connected_compact
      (hconn.image _ Complex.continuous_im.continuousOn) (hK.image Complex.continuous_im)
  have hRele : sInf (Complex.re '' K) ≤ sSup (Complex.re '' K) :=
    nonempty_Icc.mp (hRe ▸ hconn.nonempty.image Complex.re)
  have hImle : sInf (Complex.im '' K) ≤ sSup (Complex.im '' K) :=
    nonempty_Icc.mp (hIm ▸ hconn.nonempty.image Complex.im)
  rw [hRe, Real.volume_Icc, ENNReal.ofReal_eq_zero] at hre
  rw [hIm, Real.volume_Icc, ENNReal.ofReal_eq_zero] at him
  intro z hz w hw
  have hzr : z.re ∈ Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    hRe ▸ mem_image_of_mem _ hz
  have hwr : w.re ∈ Icc (sInf (Complex.re '' K)) (sSup (Complex.re '' K)) :=
    hRe ▸ mem_image_of_mem _ hw
  have hzi : z.im ∈ Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    hIm ▸ mem_image_of_mem _ hz
  have hwi : w.im ∈ Icc (sInf (Complex.im '' K)) (sSup (Complex.im '' K)) :=
    hIm ▸ mem_image_of_mem _ hw
  apply Complex.ext <;> linarith [hzr.1, hzr.2, hwr.1, hwr.2, hzi.1, hzi.2, hwi.1, hwi.2]

end CircleDomainRigidity

end

end OAI
