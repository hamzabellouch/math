import OAI.Probability.SLE.Loewner.InitialInverseRangeAt
import OAI.Probability.SLE.Loewner.SlitChartLimitUniqueness

namespace OAI

/-! Both-sided identification of the actual initial inverse-chart limits. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

theorem initialInverse_limit_eq_at (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (hs : s≠0) (ht : Tendsto t atTop (𝓝 s)) :
    EqOn F (initialInverseChart p hi h0 hH s) upperHalfPlane := by
  obtain ⟨R0,hR0⟩ := (isCompact_range p.continuous).isBounded.exists_norm_le
  let R := max R0 1
  have hR : 0<R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp (u : unitInterval) : ‖p u‖≤R := (hR0 _ (mem_range_self u)).trans (le_max_left _ _)
  rw [initialInverseChart,dite_eq_right hs]
  exact (initialSlitChart p hi h0 hH s hs).eq_inverse_of_vertical_bounds hF
    (initialInverse_limit_bijOn_at p hi h0 hH hF hlim ht)
    (fun _ hz => initialInverse_limit_im_ge p hi h0 hH hlim hz)
    hR (fun u => hp (s*u))
    (fun _ hz => initialInverse_limit_uniform_displacement p hi h0 hH hlim hz)
    (fun _ hz => initialInverse_limit_inverse_far_height p hi h0 hH hF hlim hR hp hz)

end SLEExactGauge

end

end OAI
