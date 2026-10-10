import OAI.Analysis.NumericalRange.Main

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology

def LocalClosedAnalyticBoundary (U : Set ℂ) (p : ℂ) : Prop :=
  ∃ χ : ℂ → ℂ, χ 0 = p ∧ AnalyticAt ℂ χ 0 ∧ deriv χ 0 ≠ 0 ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ U ↔ 0 < z.im) ∧
    (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → χ z ∈ frontier U) ∧
    (∀ᶠ z : ℂ in 𝓝 0, χ z ∈ closure U ↔ 0 ≤ z.im)

lemma convex_analytic_interior_coordinate {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hK : IsCompact (closure U))
    {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalAnalyticBoundary U p) :
    Nonempty (DiskCoordinate U a) := by
  have := hcv.contractibleSpace ⟨a, ha⟩
  exact analytic_domain_disk_coordinate hU
    (by change SimplyConnectedSpace U; infer_instance)
    (hK.isBounded.subset subset_closure) ha hchart

lemma convex_closed_analytic_exterior_coordinate {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hK : IsCompact (closure U))
    {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, LocalClosedAnalyticBoundary U p) :
    Nonempty (ExteriorCoordinate U) := by
  have := invertedExterior_simplyConnected hcv.closure (subset_closure ha)
  have hcharts : ∀ p ∈ frontier (invertedExterior (closure U) a),
      LocalAnalyticBoundary (invertedExterior (closure U) a) p := by
    intro p hp
    obtain ⟨hp0, hzp⟩ := invertedExterior_frontier hU hK ha hp
    obtain ⟨χ, hχ0, hχa, hχd, _, _, hχc⟩ := hchart _ hzp
    have hza : a + p⁻¹ ≠ a := by simpa using inv_ne_zero hp0
    obtain ⟨ψ, hψ0, hψa, hψd, hψs, hψb⟩ :=
      invertedExterior_local_chart hK hχ0 hχa hχd hza hχc
    exact ⟨ψ, by simpa only [add_sub_cancel_left, inv_inv] using hψ0, hψa, hψd, hψs, hψb⟩
  obtain ⟨D⟩ := analytic_domain_disk_coordinate (invertedExterior_open hK)
    (by change SimplyConnectedSpace (invertedExterior (closure U) a); infer_instance)
    (invertedExterior_bounded (hU.subset_interior_closure ha))
    (zero_mem_invertedExterior (closure U) a) hcharts
  exact exteriorCoordinate_of_disk_inversion hU hK ha
    ((hcv.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hU.interior_eq]; exact ⟨a, ha⟩)).trans hU.interior_eq) D
end CompleteCrouzeix
end

end OAI
