import OAI.Analysis.CircleDomains.Topology.PositiveRegularJordanBoundary
import OAI.Analysis.CircleDomains.Topology.RegularJordanSideChoice
import OAI.Analysis.CircleDomains.Uniformization.UniformTransverseDisplacement
import OAI.Analysis.CircleDomains.Topology.InwardFieldCollar

namespace OAI

/-! Construction of the precise regular Jordan inward collar from
regular level charts and a compactly supported transverse field, using
circle classification and the signed finite Green identity. -/
open Set Function Filter
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_small_inward_field
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f)
    (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ (W : ℂ → ℂ) (L : ℝ≥0), ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      LipschitzWith L W ∧ L < 1 ∧
      ∀ ρ ∈ Ioc (0 : ℝ) 1, ∀ z ∈ frontier (jordanInterior H),
        z+ρ • W z ∈ jordanInterior H := by
  let K := frontier (jordanInterior H)
  have hK : IsCompact K := (isCompact_closure_jordanInterior H).of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  obtain ⟨V, L, hs, hc, hV, htrans⟩ := exists_compact_transverse_field hf hK
    (fun z hz => ht z (hlevel hz))
  obtain ⟨U, hU, hKU, hside⟩ := regular_jordan_global_side H hf ht hlevel
  obtain ⟨δ, hδ, hdisp⟩ := uniform_transverse_displacement hf hs hK hU hKU htrans
  let ε : ℝ := min δ (1/(2*((L : ℝ)+1)))
  have hL0 : 0 ≤ (L : ℝ) := L.coe_nonneg
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεL : ε*(L : ℝ) < 1 := by
    have hh := (le_div_iff₀ (show 0 < 2*((L : ℝ)+1) by positivity)).mp
      (show ε ≤ 1/(2*((L : ℝ)+1)) from min_le_right _ _)
    nlinarith
  have hsmall : ‖ε‖₊*L < 1 := by
    change ‖ε‖*(L : ℝ) < 1
    simpa only [Real.norm_eq_abs, abs_of_pos hε] using hεL
  have hsmallneg : ‖-ε‖₊*L < 1 := by simpa only [nnnorm_neg] using hsmall
  have hr (ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) 1) : ρ*ε ∈ Ioc (0 : ℝ) δ :=
    ⟨mul_pos hρ.1 hε, (mul_le_of_le_one_left hε.le hρ.2).trans hεδ⟩
  rcases hside with hp | hm
  · refine ⟨(fun z => ε • V z), ‖ε‖₊*L,
      (contDiff_const (c := ε)).smul hs, hc.smul_left (f := fun _ : ℂ => ε),
      (lipschitzWith_smul ε).comp hV, hsmall, ?_⟩
    intro ρ hρ z hz
    have hh := hdisp z hz (ρ*ε) (hr ρ hρ)
    rw [smul_smul]
    exact hp _ hh.2.2.2 (by rw [← show f z = t from hlevel hz]; exact hh.2.1)
  · refine ⟨(fun z => (-ε) • V z), ‖-ε‖₊*L,
      (contDiff_const (c := -ε)).smul hs, hc.smul_left (f := fun _ : ℂ => -ε),
      (lipschitzWith_smul (-ε)).comp hV, hsmallneg, ?_⟩
    intro ρ hρ z hz
    have hh := hdisp z hz (ρ*ε) (hr ρ hρ)
    have hin := hm _ hh.2.2.1 (by rw [← show f z = t from hlevel hz]; exact hh.1)
    simpa only [smul_smul, mul_neg, neg_smul, smul_neg, sub_eq_add_neg] using hin

 theorem smoothRegularJordanCollars
    (hgreen : UnorientedFiniteCircleGreenFormula) :
    SmoothRegularJordanCollars := by
  intro H f t hf ht hlevel
  obtain ⟨γ, hγ⟩ := exists_positive_parametrization_of_regular_jordan_boundary
    hgreen H hf ht hlevel
  obtain ⟨V, L, hs, hc, hV, hL, hin⟩ := exists_small_inward_field H hf ht hlevel
  exact exists_inward_collar_of_field H hγ V hs hc hV hL hin

end CircleDomainRigidity

end

end OAI
