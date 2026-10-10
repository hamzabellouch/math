import OAI.Geometry.SurfaceImmersion.Geometry.AxisDefectJet

namespace OAI

/-! A common normal coordinate system for the two actual simple zeros. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem normalized_two_zero_axis {N : Base → Base} {U : Set Base} (hU : IsOpen U)
    (hN : ContDiffOn ℝ ∞ N U) {p q : ℝ} (hpq : p < q)
    (haxis : ∀ t ∈ Icc p q, crosscapAxis t ∈ U)
    (hz : ∀ x ∈ U, N x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q)
    (hDp : Function.Bijective (fderiv ℝ N (crosscapAxis p)))
    (hDq : Function.Bijective (fderiv ℝ N (crosscapAxis q))) :
    ∃ (d : ℝ → Base) (O : Set Base) (W : Set ℝ), ContDiff ℝ ∞ d ∧
      IsOpen O ∧ O ⊆ U ∧ IsOpen W ∧ Icc p q ⊆ W ∧ (∀ t ∈ W, crosscapAxis t ∈ O) ∧
      ContDiffOn ℝ ∞ (axisNormalizedDefect d N) O ∧
      (∀ t ∈ W, axisNormalizedDefect d N (crosscapAxis t) = ![(t-p)*(t-q),0]) ∧
      (∀ x ∈ O, axisNormalizedDefect d N x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis p)) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis q)) ∧
      (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis p) (![1,0] : Base)) 1 ≠ 0 ∧
      (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis q) (![1,0] : Base)) 1 ≠ 0 := by
  obtain ⟨d,V,hd,hV,hKV,hn,he⟩ := two_zero_axis_factor hU hN hpq haxis hz hDp hDq
  let O := U ∩ {x : Base | d (x 1) ≠ 0}
  have hO : IsOpen O := hU.inter
    (isOpen_ne.preimage (hd.continuous.comp (continuous_apply 1)))
  let W := V ∩ crosscapAxis ⁻¹' O
  have hW : IsOpen W := hV.inter (hO.preimage crosscapAxis.continuous)
  have hKW : Icc p q ⊆ W := by
    intro t ht
    refine ⟨hKV ht,haxis t ht,?_⟩
    simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using hn t ht
  have hGO : ContDiffOn ℝ ∞ (axisNormalizedDefect d N) O := by
    intro x hx
    exact (axisNormalizedDefect_smoothAt hd (hN.contDiffAt (hU.mem_nhds hx.1)) hx.2).contDiffWithinAt
  have hGa : ∀ t ∈ W, axisNormalizedDefect d N (crosscapAxis t) = ![(t-p)*(t-q),0] := by
    intro t ht
    apply axisNormalizedDefect_axis
    · simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using ht.2.2
    · exact he t ht.1
  have hpW := hKW (left_mem_Icc.mpr hpq.le)
  have hqW := hKW (right_mem_Icc.mpr hpq.le)
  have hGp := hGO.contDiffAt (hO.mem_nhds hpW.2)
  have hGq := hGO.contDiffAt (hO.mem_nhds hqW.2)
  have hDpG : Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis p)) :=
    axisNormalizedDefect_derivative_bijective hd
      (hN.contDiffAt (hU.mem_nhds hpW.2.1)) hpW.2.2
      ((hz _ hpW.2.1).mpr (Or.inl rfl)) hDp
  have hDqG : Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis q)) :=
    axisNormalizedDefect_derivative_bijective hd
      (hN.contDiffAt (hU.mem_nhds hqW.2.1)) hqW.2.2
      ((hz _ hqW.2.1).mpr (Or.inr rfl)) hDq
  refine ⟨d,O,W,hd,hO,inter_subset_left,hW,hKW,fun _ ht => ht.2,hGO,hGa,?_,hDpG,hDqG,
    normalized_axis_transverse_nonzero hGp hW hpW hGa hDpG,
    normalized_axis_transverse_nonzero hGq hW hqW hGa hDqG⟩
  intro x hx
  change (planeComplexFrame (d (x 1))).inverse (N x) = 0 ↔ _
  rw [←(map_zero (planeComplexFrame (d (x 1))).inverse)]
  exact (planeComplexFrame_invertible hx.2).inverse.injective.eq_iff.trans (hz x hx.1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
