import Mathlib
import OAI.Analysis.Crouzeix.ConvexApproximation
import OAI.Analysis.Crouzeix.ExteriorRiemann

namespace OAI

/-! Exterior Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem closed_side_of_side (e : OpenPartialHomeomorph ℂ ℂ) {U : Set ℂ}
    (hs : ∀ z ∈ e.source, e z ∈ U ↔ 0 < z.im) :
    ∀ z ∈ e.source, e z ∈ closure U ↔ 0 ≤ z.im := by
  have hi : e.IsImage {z : ℂ | 0 < z.im} U := fun _ hz => hs _ hz
  intro z hz
  simpa only [closure_setOfPred_lt_im, mem_ofPred_eq] using hi.closure hz

theorem frontier_invertedExterior {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (a : ℂ) {z : ℂ}
    (hz : z ∈ frontier (invertedExterior (closure U) a)) :
    z ≠ 0 ∧ a + z⁻¹ ∈ frontier U := by
  have hI := isOpen_invertedExterior hb.isCompact_closure a
  have hzn : z ∉ invertedExterior (closure U) a := by
    simpa only [hI.interior_eq] using hz.2
  have hz0 : z ≠ 0 := fun he => hzn (Or.inl he)
  have hzc : a + z⁻¹ ∈ closure U := by
    by_contra hn
    exact hzn (Or.inr hn)
  refine ⟨hz0, hzc, ?_⟩
  rw [hU.interior_eq]
  intro hzu
  have hn : {w : ℂ | w ≠ 0 ∧ a + w⁻¹ ∈ U} ∈ 𝓝 z :=
    inter_mem (isClosed_singleton.isOpen_compl.mem_nhds hz0)
      ((continuousAt_const.add (continuousAt_inv₀ hz0)).preimage_mem_nhds (hU.mem_nhds hzu))
  obtain ⟨w, hw, hwI⟩ := mem_closure_iff_nhds.mp hz.1 _ hn
  exact (hwI.resolve_left hw.1) (subset_closure hw.2)

theorem boundaryChart_invertedExterior {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) {a : ℂ} (_ha : a ∈ U)
    (hc : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p))
    {p : ℂ} (hp : p ∈ frontier (invertedExterior (closure U) a)) :
    Nonempty (BoundaryChart (invertedExterior (closure U) a) p) := by
  obtain ⟨hp0, hpf⟩ := frontier_invertedExterior hU hb a hp
  obtain ⟨c⟩ := hc _ hpf
  let N : Set ℂ := {z | -z ∈ c.e.source ∧ c.e (-z) ≠ a}
  have hNo : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact inter_mem ((continuous_neg).continuousAt.preimage_mem_nhds
      (c.e.open_source.mem_nhds hz.1))
      (((c.analytic _ hz.1).continuousAt.comp continuous_neg.continuousAt).preimage_mem_nhds
        (isClosed_singleton.isOpen_compl.mem_nhds hz.2))
  have hN0 : (0 : ℂ) ∈ N := by
    refine ⟨by simpa only [neg_zero] using c.zero_mem, ?_⟩
    simp only [neg_zero, c.at_zero, ne_eq, add_eq_left, inv_eq_zero]
    exact hp0
  let χ : ℂ → ℂ := fun z => (c.e (-z) - a)⁻¹
  have hχa : AnalyticOnNhd ℂ χ N := by
    intro z hz
    exact (((c.analytic _ hz.1).comp (show AnalyticAt ℂ (fun z : ℂ => -z) z from
      analyticAt_id.neg)).sub analyticAt_const).inv (sub_ne_zero.mpr hz.2)
  have hχi : InjOn χ N := by
    intro z hz w hw he
    exact neg_injective (c.e.injOn hz.1 hw.1
      (sub_left_injective (inv_injective he)))
  let d := (hχa 0 hN0).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (deriv_ne_zero_of_injOn hNo hχa.differentiableOn hχi hN0)
  let e := (d.toOpenPartialHomeomorph χ).restrOpen N hNo
  have heN : e.source ⊆ N := inter_subset_right
  have hea : AnalyticOnNhd ℂ e e.source := hχa.mono heN
  have he0 : (0 : ℂ) ∈ e.source := ⟨d.mem_toOpenPartialHomeomorph_source, hN0⟩
  have hs : ∀ z ∈ e.source,
      e z ∈ invertedExterior (closure U) a ↔ 0 < z.im := by
    intro z hz
    have hzN := heN hz
    change ((c.e (-z) - a)⁻¹ = 0 ∨ a + ((c.e (-z) - a)⁻¹)⁻¹ ∉ closure U) ↔ _
    simp only [inv_eq_zero, sub_eq_zero, hzN.2, false_or, inv_inv, add_sub_cancel,
      c.closed_side _ hzN.1, neg_im, not_le, neg_lt_zero]
  refine ⟨⟨e, he0, ?_, hea, analyticOnNhd_symm e hea, hs, closed_side_of_side e hs⟩⟩
  change (c.e (-0) - a)⁻¹ = p
  simp only [neg_zero, c.at_zero, add_sub_cancel_left, inv_inv]

theorem exists_inverted_exterior_collar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hconv : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    (hc : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (ρ : ℝ) (f h : ℂ → ℂ),
      IsOpen V ∧ closure (invertedExterior (closure U) a) ⊆ V ∧ 1 < ρ ∧
      AnalyticOnNhd ℂ f V ∧ AnalyticOnNhd ℂ h (ball 0 ρ) ∧
      InjOn f V ∧ InjOn h (ball 0 ρ) ∧
      BijOn f (invertedExterior (closure U) a) (ball 0 1) ∧
      BijOn h (ball 0 1) (invertedExterior (closure U) a) ∧
      BijOn f (closure (invertedExterior (closure U) a)) (closedBall 0 1) ∧
      BijOn h (closedBall 0 1) (closure (invertedExterior (closure U) a)) ∧
      InvOn h f (invertedExterior (closure U) a) (ball 0 1) ∧ f 0 = 0 ∧ h 0 = 0 ∧
      (∀ z ∈ frontier (invertedExterior (closure U) a), ‖f z‖ = 1) ∧
      InvOn h f V (f '' V) ∧ ball 0 ρ ⊆ f '' V := by
  apply exists_conformal_collar (isOpen_invertedExterior hb.isCompact_closure a)
    (isBounded_invertedExterior (interior_mono subset_closure (hU.interior_eq.symm ▸ ha)))
    (isSimplyConnected_invertedExterior hconv.closure (subset_closure ha))
    (zero_mem_invertedExterior _ _)
  exact fun p hp => boundaryChart_invertedExterior hU hb ha hc hp

end CrouzeixHilbert.Conformal

end

end OAI
