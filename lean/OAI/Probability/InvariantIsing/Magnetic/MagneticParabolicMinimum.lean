import OAI.Probability.InvariantIsing.Magnetic.MagneticMinimumCalculus
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Minimum comparison on the closed mean-spin interval. Diffusion and
drift may degenerate at the two endpoints, where both coefficients vanish. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma parabolic_minimum_nonneg {T : ℝ} (hT : 0 ≤ T)
    (W Wt Wx Wxx A B C : ℝ × ℝ → ℝ)
    (hW : ContinuousOn W (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x))
    (hdt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t)
    (hdx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x)
    (hdxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x)
    (hA : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ A p)
    (hC : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, C p < 0)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) T,
      A (t, -1) = 0 ∧ B (t, -1) = 0 ∧ A (t, 1) = 0 ∧ B (t, 1) = 0)
    (hPDE : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Wxx p + B p * Wx p + C p * W p ≤ Wt p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ W p := by
  intro p hp
  by_contra hn
  have hpneg : W p < 0 := lt_of_not_ge hn
  obtain ⟨q, hq, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ⟨(0, 0), by exact ⟨⟨le_rfl, hT⟩, by constructor <;> norm_num⟩⟩ hW
  have hqneg : W q < 0 := (hmin hp).trans_lt hpneg
  have hqt : 0 < q.1 := by
    have hqn : q.1 ≠ 0 := by
      intro he
      have hh := hinit q.2 hq.2
      have hqe : q = (0, q.2) := Prod.ext he rfl
      rw [hqe] at hqneg
      linarith
    exact lt_of_le_of_ne hq.1.1 (Ne.symm hqn)
  have htime : ∀ᶠ t in 𝓝[<] q.1, W q ≤ W (t, q.2) := by
    have hn0 : ∀ᶠ t in 𝓝[<] q.1, 0 < t :=
      (show ∀ᶠ t : ℝ in 𝓝 q.1, 0 < t from Ioi_mem_nhds hqt).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hn0, self_mem_nhdsWithin] with t ht0 htt
    exact hmin ⟨⟨ht0.le, htt.le.trans hq.1.2⟩, hq.2⟩
  have htderiv : Wt q ≤ 0 := derivativeWithin_nonpos_at_left_min
    (hdt q.1 ⟨hqt, hq.1.2⟩ q.2 hq.2) htime
  have hqC : 0 < C q * W q := mul_pos_of_neg_of_neg (hC q hq) hqneg
  have hqp : q ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1 := ⟨⟨hqt, hq.1.2⟩, hq.2⟩
  by_cases hleft : q.2 = -1
  · have hb := hboundary q.1 hq.1
    have hpde := hPDE q hqp
    have hqe : q = (q.1, -1) := Prod.ext rfl hleft
    rw [hqe, hb.1, hb.2.1, zero_mul, zero_mul, zero_add, zero_add] at hpde
    rw [hqe] at htderiv hqC
    linarith
  by_cases hright : q.2 = 1
  · have hb := hboundary q.1 hq.1
    have hpde := hPDE q hqp
    have hqe : q = (q.1, 1) := Prod.ext rfl hright
    rw [hqe, hb.2.2.1, hb.2.2.2, zero_mul, zero_mul, zero_add, zero_add] at hpde
    rw [hqe] at htderiv hqC
    linarith
  have hqi : q.2 ∈ Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hq.2.1 (Ne.symm hleft), lt_of_le_of_ne hq.2.2 hright⟩
  have hm : IsLocalMin (fun x => W (q.1, x)) q.2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hqi] with x hx
    exact hmin ⟨hq.1, ⟨hx.1.le, hx.2.le⟩⟩
  have hx0 : Wx q = 0 := hm.hasDerivAt_eq_zero (hdx q.1 hq.1 q.2 hqi)
  have hxx : 0 ≤ Wxx q := by
    apply second_derivative_nonneg_at_local_min hm ?_ (hdxx q.1 hq.1 q.2 hqi)
    filter_upwards [isOpen_Ioo.mem_nhds hqi] with x hx
    exact hdx q.1 hq.1 x hx
  have hprod : 0 ≤ A q * Wxx q := mul_nonneg (hA q hq) hxx
  have hpde := hPDE q hqp
  rw [hx0, mul_zero, add_zero] at hpde
  linarith

end InvariantIsing

end

end OAI
