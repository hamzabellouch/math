import OAI.Analysis.CircleDomains.Sobolev.InversePieceJacobian
import OAI.Analysis.CircleDomains.Sobolev.CoareaInput

namespace OAI

/-! Exact weighted scalar coarea on a regular measurable inverse piece. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverse_piece_fiber_eq {F : ℂ → ℂ} {f : ℂ → ℝ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (he : ∀ z, (F z).re = f z)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    (hT : MeasurableSet T) (hb : IsBounded T) (hTS : T ⊆ F '' S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) (t : ℝ) :
    weightedScalarLevelLength ((invFunOn F S) '' T) f q t =
      ∫⁻ s, inversePieceWeight F S T q (coareaVerticalLine t s) := by
  have hset : ((invFunOn F S) '' T) ∩ {z | f z = t} =
      ((invFunOn F S) ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hfy⟩
      have hyr : y.re = t := by
        calc
          y.re = (F (invFunOn F S y)).re := congrArg Complex.re (invFunOn_eq (hTS hy)).symm
          _ = f (invFunOn F S y) := he _
          _ = t := hfy
      have hyline : coareaVerticalLine t y.im = y := by
        apply Complex.ext <;> simp [hyr]
      exact ⟨y.im, by rwa [mem_preimage, hyline], by simp only [comp_apply, hyline]⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨coareaVerticalLine t s, hs, rfl⟩, ?_⟩
      change f (invFunOn F S (coareaVerticalLine t s)) = t
      rw [← he, invFunOn_eq (hTS hs), coareaVerticalLine_re]
  rw [weightedScalarLevelLength, hset,
    weighted_inverse_piece_vertical_curve hF hd hi hT hb hTS t hq]
  rw [← lintegral_indicator (hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable)]
  apply lintegral_congr
  intro s
  by_cases hs : coareaVerticalLine t s ∈ T <;> simp [inversePieceWeight, hs]

lemma inverse_piece_weighted_coarea {F : ℂ → ℂ} {f : ℂ → ℝ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (he : ∀ z, (F z).re = f z)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    (hT : MeasurableSet T) (hb : IsBounded T) (hTS : T ⊆ F '' S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    WeightedScalarCoareaIdentity ((invFunOn F S) '' T) f q := by
  let W := inversePieceWeight F S T q
  have hW : Measurable W := measurable_inversePieceWeight hF hT hTS hq
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => W (Complex.measurableEquivRealProd.symm p)
  have hH : Measurable H := hW.comp Complex.measurableEquivRealProd.symm.measurable
  have hline (t s : ℝ) : coareaVerticalLine t s = Complex.measurableEquivRealProd.symm (t,s) := by
    apply Complex.ext <;> simp
  have hfun : weightedScalarLevelLength ((invFunOn F S) '' T) f q = fun t => ∫⁻ s, H (t,s) := by
    funext t
    rw [inverse_piece_fiber_eq hF he hd hi hT hb hTS hq]
    simp only [H, W, hline]
  refine ⟨by rw [hfun]; exact hH.lintegral_prod_right'.aemeasurable, ?_⟩
  rw [hfun, ← lintegral_prod H hH.aemeasurable, ← Measure.volume_eq_prod]
  have hm := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).lintegral_comp hW
  exact hm.trans (inverse_piece_energy_eq hF he hd hi hT hTS q).symm

end CircleDomainRigidity

end

end OAI
