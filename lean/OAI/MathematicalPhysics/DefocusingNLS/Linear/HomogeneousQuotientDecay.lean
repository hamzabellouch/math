import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralQuotientDecay
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialOutgoingBoundary

namespace OAI

/-! # Gauge decay from eventual normalized outgoing bounds -/

open Set Filter Topology Asymptotics

namespace DefocusingNLS

theorem homogeneousQuotient_energy_decay (ν : ℂ) (hν : ν.re ≤ -8)
    (Y Q : ℝ → ℂ × ℂ) (M K D : ℝ)
    (hY : ∀ᶠ t in atTop, ‖Y t‖ ≤ M)
    (hQ : ∀ᶠ t in atTop, ‖((Q t).1)⁻¹‖ ≤ K)
    (hQ' : ∀ᶠ t in atTop, ‖(Q t).2‖ ≤ D)
    (hQ0 : ∀ᶠ t in atTop, (Q t).1 ≠ 0)
    (hYd : ∀ᶠ t in atTop, HasDerivAt (fun s => (Y s).1) (Y t).2 t)
    (hQd : ∀ᶠ t in atTop, HasDerivAt (fun s => (Q s).1) (Q t).2 t) :
    let F := fun r => (spectralQuotientJet ν Y Q r).1
    F =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv F =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ)) ∧
      ∀ᶠ r in atTop, DifferentiableAt ℝ F r := by
  intro F
  have hb := Real.tendsto_log_atTop.eventually (hY.and (hQ.and hQ'))
  have hv : F =O[atTop] (fun r : ℝ => r ^ ν.re) := by
    apply IsBigO.of_bound (M * K)
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _), mul_comm] using
      (spectralQuotientJet_bounds ν Y Q M K D r hr0 hr.1 hr.2.1 hr.2.2).1
  have hd : (fun r => (spectralQuotientJet ν Y Q r).2) =O[atTop]
      (fun r : ℝ => r ^ (ν.re - 1)) := by
    apply IsBigO.of_bound (((‖ν‖ + 1) * M) * K + M * D * K ^ 2)
    filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr0 _), mul_comm] using
      (spectralQuotientJet_bounds ν Y Q M K D r hr0 hr.1 hr.2.1 hr.2.2).2
  have hp (a b : ℝ) (hab : a ≤ b) :
      (fun r : ℝ => r ^ a) =O[atTop] (fun r : ℝ => r ^ b) := by
    apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _)]
    exact Real.rpow_le_rpow_of_exponent_le hr hab
  have hder : ∀ᶠ r in atTop, HasDerivAt F (spectralQuotientJet ν Y Q r).2 r := by
    filter_upwards [Real.tendsto_log_atTop.eventually (hQ0.and (hYd.and hQd)),
      eventually_gt_atTop (0 : ℝ)] with r hr hr0
    exact spectralQuotientJet_hasDerivAt ν Y Q r hr0 hr.1 hr.2.1 hr.2.2
  refine ⟨hv.trans (hp _ _ hν), ?_, hder.mono (fun _ h => h.differentiableAt)⟩
  apply (hd.trans (hp _ _ (by linarith : ν.re - 1 ≤ -9))).congr' _ EventuallyEq.rfl
  exact hder.mono (fun _ h => h.deriv.symm)

theorem homogeneousComplexEnergyDecay_real
    (F : ℝ → ℂ)
    (hF : F =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)))
    (hdF : deriv F =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ)))
    (hfd : ∀ᶠ r in atTop, DifferentiableAt ℝ F r)
    (L : ℂ →L[ℝ] ℝ) : HasRadialEnergyDecay (fun r => L (F r)) := by
  have hb (G : ℝ → ℂ) : (fun r => L (G r)) =O[atTop] G :=
    IsBigO.of_bound ‖L‖ (Eventually.of_forall (fun r => L.le_opNorm (G r)))
  refine ⟨(hb F).trans hF, ?_⟩
  apply ((hb (deriv F)).trans hdF).congr' _ EventuallyEq.rfl
  filter_upwards [hfd] with r hr
  exact (L.hasFDerivAt.comp_hasDerivAt r hr.hasDerivAt).deriv.symm

theorem homogeneousQuotient_energy_decay_of_limits
    (ν : ℂ) (hν : ν.re ≤ -8) (Y Q : ℝ → ℂ × ℂ) (y₀ : ℂ × ℂ) (q₀ : ℂ)
    (hq₀ : q₀ ≠ 0) (hy : Tendsto Y atTop (𝓝 y₀))
    (hq : Tendsto Q atTop (𝓝 (q₀, 0)))
    (hYd : ∀ᶠ t in atTop, HasDerivAt (fun s => (Y s).1) (Y t).2 t)
    (hQd : ∀ᶠ t in atTop, HasDerivAt (fun s => (Q s).1) (Q t).2 t) :
    let F := fun r => (spectralQuotientJet ν Y Q r).1
    F =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv F =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ)) ∧
      ∀ᶠ r in atTop, DifferentiableAt ℝ F r := by
  have hqi := (hq.fst_nhds.inv₀ hq₀).norm
  have hyb := (hy.norm.eventually (gt_mem_nhds
    (show ‖y₀‖ < ‖y₀‖ + 1 by linarith))).mono (fun _ h => h.le)
  have hqib := (hqi.eventually (gt_mem_nhds
    (show ‖q₀⁻¹‖ < ‖q₀⁻¹‖ + 1 by linarith))).mono (fun _ h => h.le)
  have hqdb := (hq.snd_nhds.norm.eventually (gt_mem_nhds
    (show ‖(0 : ℂ)‖ < 1 by norm_num))).mono (fun _ h => h.le)
  have hqn := hq.fst_nhds.eventually (eventually_ne_nhds hq₀)
  exact homogeneousQuotient_energy_decay ν hν Y Q (‖y₀‖ + 1) (‖q₀⁻¹‖ + 1) 1
    hyb hqib hqdb hqn hYd hQd

theorem homogeneousQuotient_value (ν μ : ℂ) (Y Q : ℝ → ℂ × ℂ) (r : ℝ) :
    (spectralPhysicalJet (μ + ν) Y r).1 /
      (Complex.exp (μ * (Real.log r : ℂ)) * (Q (Real.log r)).1) =
        (spectralQuotientJet ν Y Q r).1 := by
  have he : Complex.exp ((μ + ν) * (Real.log r : ℂ)) =
      Complex.exp (μ * (Real.log r : ℂ)) * Complex.exp (ν * (Real.log r : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  change Complex.exp ((μ + ν) * (Real.log r : ℂ)) * (Y (Real.log r)).1 /
    (Complex.exp (μ * (Real.log r : ℂ)) * (Q (Real.log r)).1) = _
  rw [he]
  simp only [spectralQuotientJet, div_eq_mul_inv, mul_inv_rev]
  have hn := Complex.exp_ne_zero (μ * (Real.log r : ℂ))
  calc
    _ = (Complex.exp (μ * (Real.log r : ℂ)) *
        (Complex.exp (μ * (Real.log r : ℂ)))⁻¹) *
        (Complex.exp (ν * (Real.log r : ℂ)) * ((Y (Real.log r)).1 * (Q (Real.log r)).1⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hn, one_mul]

theorem homogeneousEventuallyEq_deriv_atTop {F G : ℝ → ℂ}
    (h : F =ᶠ[atTop] G) : deriv F =ᶠ[atTop] deriv G := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp h
  filter_upwards [eventually_gt_atTop T] with r hr
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hr] with s hs
  exact hT s hs.le

theorem homogeneousComplexEnergyDecay_congr {F G : ℝ → ℂ}
    (h : F =ᶠ[atTop] G)
    (hF : F =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)))
    (hdF : deriv F =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ))) :
    G =O[atTop] (fun r : ℝ => r ^ (-8 : ℝ)) ∧
      deriv G =O[atTop] (fun r : ℝ => r ^ (-9 : ℝ)) := by
  exact ⟨hF.congr' h EventuallyEq.rfl,
    hdF.congr' (homogeneousEventuallyEq_deriv_atTop h) EventuallyEq.rfl⟩

end DefocusingNLS

end OAI
