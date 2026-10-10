import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactPhysicalCorrections

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

theorem exists_physical_moments_in_open
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U O : Set Coord3} (hO : IsOpen O) (hne : O.Nonempty) (hOU : O⊆U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) (m : Coord3) :
    ∃ r : PhysicalSourcePair,CompactSmoothPair r ∧ PairSupported r O ∧
      physicalSourceMoment u r=m := by
  obtain ⟨p,hp⟩ := hne
  obtain ⟨B,_⟩ := exists_regular_correction_box hu hO hp (hD p (hOU hp))
  obtain ⟨r₀,r₁,hr₀,hr₁,hc₀,hc₁,hs₀,hs₁,hm₀,hm₁,hmt⟩ :=
    physical_overlap_moment_inverse B.chart B.smooth B.inverse_smooth B.widths B.subset_source m
  let r : PhysicalSourcePair := ![r₀,r₁]
  have hr : CompactSmoothPair r := by
    intro j; fin_cases j
    · exact ⟨hr₀,hc₀⟩
    · exact ⟨hr₁,hc₁⟩
  have hs : PairSupported r B.chart.target := by
    intro j; fin_cases j
    · exact hs₀
    · exact hs₁
  refine ⟨r,hr,hs.mono B.target_subset,?_⟩
  ext i
  fin_cases i
  · exact hm₀
  · exact hm₁
  · change (∫ x,u x 1*r₀ x-u x 0*r₁ x)=m 2
    rw [←hmt]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈B.chart.target
    · have he := B.potentials hx
      rw [he]
      rfl
    · have h₀ : r₀ x=0 := Function.notMem_support.mp (fun hh => hx (hs₀ (subset_tsupport r₀ hh)))
      have h₁ : r₁ x=0 := Function.notMem_support.mp (fun hh => hx (hs₁ (subset_tsupport r₁ hh)))
      simp [h₀,h₁]

lemma RegularCorrectionBox.transfer
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p))
    (B C : RegularCorrectionBox u U) (hBC : (B.region∩C.region).Nonempty)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r B.region) :
    ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
      physicalSourceMoment u q=physicalSourceMoment u r ∧ PhysicallyCorrectable u U (r-q) := by
  obtain ⟨q,hq,hqs,hm⟩ := exists_physical_moments_in_open hu
    (B.region_open.inter C.region_open) hBC (inter_subset_left.trans B.region_subset)
    hD (physicalSourceMoment u r)
  refine ⟨q,hq,hqs.mono inter_subset_right,hm,?_⟩
  apply B.correct hu (hr.sub hq) (hs.sub (hqs.mono inter_subset_left))
  rw [physicalSourceMoment_sub hu.continuous hr hq,hm,sub_self]

lemma regular_correction_boxes_cover
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) :
    (⋃ B : RegularCorrectionBox u U,B.region)=U := by
  apply Subset.antisymm
  · exact iUnion_subset fun B => B.region_subset
  · intro p hp
    obtain ⟨B,hB⟩ := exists_regular_correction_box hu hU hp (hD p hp)
    exact mem_iUnion.mpr ⟨B,hB⟩

lemma regular_correction_boxes_chain
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) (B C : RegularCorrectionBox u U) :
    Relation.TransGen (fun P Q : RegularCorrectionBox u U => (P.region∩Q.region).Nonempty) B C := by
  have hc : IsPreconnected (⋃ B : RegularCorrectionBox u U,B.region) := by
    rwa [regular_correction_boxes_cover hu hU hD]
  exact hc.transGen_of_iUnion (fun B => B.region_open) B C B.region_nonempty C.region_nonempty

theorem regular_source_transport
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) (B C : RegularCorrectionBox u U)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : PairSupported r B.region) :
    ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
      physicalSourceMoment u q=physicalSourceMoment u r ∧ PhysicallyCorrectable u U (r-q) := by
  have hp := regular_correction_boxes_chain hu hU hUc hD B C
  induction hp with
  | single h => exact B.transfer hu hD _ h hr hs
  | @tail C D hpath hCD ih =>
    obtain ⟨q,hq,hqs,hm,hcorr⟩ := ih
    obtain ⟨s,hss,hssup,hm',hcorr'⟩ := C.transfer hu hD D hCD hq hqs
    refine ⟨s,hss,hssup,hm'.trans hm,?_⟩
    have ht := hcorr.add hu hcorr'
    simpa only [sub_add_sub_cancel] using ht

end ScalarConductivity

end
end

end OAI
