import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfileSeries

namespace OAI

/-! Actual compact automorphic sections attached to nonzero Fourier tests. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaFourierProfileSeries_core (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ),W v=0) :
    ∃ (H : ℝ) (S : Finset SL(2,Eisenstein)),∀ p : CubicThetaPoint,
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S H →
        cubicThetaFourierProfileSeries h p.val W=0 := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  let H := max 1 B
  obtain ⟨S,hS⟩ := cubicThetaHeightBand_core (le_max_left 1 B)
  refine ⟨H,S,fun p hp => ?_⟩
  suffices hz : ∀ r,cubicThetaFourierProfileTerm h r p.val W=0 by
    simp only [cubicThetaFourierProfileSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤1
  · exact cubicThetaFourierProfileTerm_zero h r p.val W (hW _ hlo)
  by_cases hz : W (r.height p.val)=0
  · exact cubicThetaFourierProfileTerm_zero h r p.val W hz
  have hhi : r.height p.val≤H :=
    (hB (mem_image_of_mem id (subset_closure hz))).trans (le_max_right 1 B)
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; exact hhi)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

def cubicThetaFourierProfileSection (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ),W v=0) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaFourierProfileSeries h p.val W,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have hc := (cubicThetaFourierProfileSeries_continuousOn h W hW).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact hc.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaFourierProfileSeries_automorphy h g p.property W⟩

lemma cubicThetaFourierProfileSection_compact (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ),W v=0) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaFourierProfileSection h W hW)) := by
  obtain ⟨H,S,hS⟩ := cubicThetaFourierProfileSeries_core h W hW
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S H)
  intro q hq
  by_contra hn
  have hz := hS (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaFourierProfileSeries h (cubicThetaQuotientLift q).val W‖=0
  rw [hz,norm_zero]

lemma cubicThetaFourierProfileTerm_zeroRow (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaFourierProfileTerm h cubicThetaZeroRow p W=
      W p.2*cubicThetaHorizontalCharacter h p.1 := by
  have hrow : cubicThetaBottomRow cubicThetaZeroRow.completion=cubicThetaBottomRow 1 := by
    rw [cubicThetaZeroRow.completion_row]
    rfl
  have hc := cubicThetaHorizontalCharacter_completion h cubicThetaZeroRow.completion 1
    hrow (⟨p,hp⟩:CubicThetaPoint)
  change cubicThetaHorizontalCharacter h
    (cubicThetaMobius (cubicThetaPrincipalComplex cubicThetaZeroRow.completion) p).1=
      cubicThetaHorizontalCharacter h
        (cubicThetaMobius (cubicThetaPrincipalComplex 1) p).1 at hc
  rw [map_one,cubicThetaMobius_one] at hc
  unfold cubicThetaFourierProfileTerm
  rw [hc]
  congr 1
  simp [cubicThetaRadialProfileTerm,CubicThetaBottomRow.height,CubicThetaBottomRow.phase,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

theorem cubicThetaFourierProfileSeries_high (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ),W v=0) {p : ℂ × ℝ} (hp : 1<p.2) :
    cubicThetaFourierProfileSeries h p W=W p.2*cubicThetaHorizontalCharacter h p.1 := by
  have he : cubicThetaFourierProfileSeries h p W=
      cubicThetaFourierProfileTerm h cubicThetaZeroRow p W := by
    apply tsum_eq_single
    intro r hr
    by_contra hn
    have hh : 1<r.height p := by
      by_contra ht
      exact hn (cubicThetaFourierProfileTerm_zero h r p W (hW _ (le_of_not_gt ht)))
    exact hr ((CubicThetaBottomRow.c_zero_iff r).mp (r.high_height_c_zero hp hh))
  rw [he]
  exact cubicThetaFourierProfileTerm_zeroRow h W (lt_trans zero_lt_one hp)

end CubicFirstMoment

end

end OAI
