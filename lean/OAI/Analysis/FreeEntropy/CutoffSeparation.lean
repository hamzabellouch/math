import OAI.Analysis.FreeEntropy.MicrostatesLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem chosen_cutoff_real_bound {h R δ Δ β : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hβ : (β:EReal)<chiCutoff (Model.τ chosenP) (Model.X chosenP h) R) :
    (β:EReal)≤chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  obtain ⟨D,hDm,hD0,hvol⟩ := exists_microstate_dimensions (Model.τ chosenP) (Model.X chosenP h) hβ
  let S := fun k => diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)
  have hs k : MeasurableSet (S k) := diagonalMicrostates_measurable _ _ _ _ _
  have hv0 k : volume (S k)≠0 := matrixVolumeEntropy_ne_bot_volume (hD0 k) _
    (ne_bot_of_gt ((EReal.bot_lt_coe β).trans (hvol k)))
  have hvt k : volume (S k)≠⊤ := ne_of_lt (microstates_volume_lt_top (Model.τ chosenP) (Model.X chosenP h) R hR k (D k) _)
  let μ := fun k => cond volume (S k)
  have hprob : ∀k,IsProbabilityMeasure (μ k) := fun k => cond_isProbabilityMeasure_of_finite (hv0 k) (hvt k)
  let : ∀k,IsProbabilityMeasure (μ k) := hprob
  have hμ k : ∀ᵐa ∂μ k,a∈S k := ae_cond_mem (hs k)
  have hn k : (S k).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    apply hv0 k
    rw [he,measure_empty]
  have hinit (k : ℕ) : β≤normalizedMatrixEntropy (μ k) (chosenStart h) := by
    have hnorm : ∀ᵐa ∂μ k,‖a‖≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R :=
      FreeTensor.diagonalMicrostates_norm_ae (Model.X chosenP h) hR μ hμ k
    have hb := normalizedMatrixEntropy_cond_lower (hD0 k) (S k) (hv0 k) (hvt k)
      (show 0≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R by positivity) hnorm (chosenStart_pos hh0)
    have he : β<((D k:ℝ)^2)⁻¹*Real.log (volume (S k)).toReal+((chosenP+1:ℕ):ℝ)/2*Real.log (D k) := by
      apply EReal.coe_lt_coe_iff.mp
      have hbvol : (β:EReal)< matrixVolumeEntropy (S k) := hvol k
      rwa [matrixVolumeEntropy_coe (S k) (hv0 k) (hvt k)] at hbvol
    exact he.le.trans (by simpa only [zpow_neg,zpow_ofNat] using hb)
  have hterm := chosen_terminal_gaussian hD0 hDm.tendsto_atTop hh0 hh1 hR hδ hΔ hδΔ hsep hq hh hn μ hμ
  have hflow := Model.matrixFlow_limit chosenP chosenP_ge_two hD0 hDm.tendsto_atTop hh0 hR hn μ hμ
    (chosenStart_pos hh0) (chosenStart_le_time hh1) hinit hterm
  exact flow_to_chiStar_gap hh0 hh1 hflow
 theorem chosen_cutoff_bound {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h))) :
    chiCutoff (Model.τ chosenP) (Model.X chosenP h) R≤
      chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  by_contra he
  obtain ⟨β,hb,hb'⟩ := EReal.exists_between_coe_real (lt_of_not_ge he)
  exact (not_lt_of_ge (chosen_cutoff_real_bound hh0 hh1 hR hδ hΔ hδΔ hsep hq hh hb')) hb
 theorem chosen_chi_bound {h δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h))) :
    chi (Model.τ chosenP) (Model.X chosenP h)≤
      chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  apply iSup_le
  intro R
  exact chosen_cutoff_bound hh0 hh1 R.property.le hδ hΔ hδΔ hsep hq hh
end FiniteEntropySeparation

end

end OAI
