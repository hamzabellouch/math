import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVariation
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedLowCoefficients

namespace OAI

/-! A low-jet coefficient variation is linear in the varied map and loses
only the two derivatives in its second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_low_coefficient_vector {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → E} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn (hK.prod isCompact_Icc) hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

theorem compact_coefficient_variation {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G H : Base → Space) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      Set.MapsTo (lowJet G) U K → WeightedBound U s m B (lowJet G) →
      WeightedBound U s (m + 2) C H → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      WeightedBound U s m (D * C / s ^ 2)
        (fun p => fderiv ℝ c (lowJet G p, t) (variationLowJet H p, 0)) := by
  have hdc : ContDiffOn ℝ ∞ (fderiv ℝ c) (O ×ˢ Set.univ) :=
    hc.fderiv_of_isOpen (hO.prod isOpen_univ) (m := ∞) (by simp)
  obtain ⟨D, hD, hb⟩ := compact_low_coefficient_vector hU hO hK hKO hdc m B hB
  refine ⟨2 ^ m * D, by positivity, ?_⟩
  intro G H s C hs hs1 hC hG hH hGK hGb hHb t ht
  have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
  have hdb := hb (lowJet G) s hs (lowJet_smooth hG).contDiffOn hGK hGb t ht
  have hvb := weighted_variationLowJet hU hH hs hs1 hC m hHb
  have hpair : WeightedBound U s m (C / s ^ 2)
      (fun p => (variationLowJet H p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hvb.linear hU.uniqueDiffOn hs.le (variationLowJet_smooth hH).contDiffOn
        (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hds : ContDiffOn ℝ ∞ (fun p => fderiv ℝ c (lowJet G p, t)) U :=
    hdc.comp ((lowJet_smooth hG).contDiffOn.prodMk contDiffOn_const)
      (fun p hp => ⟨hQ hp, Set.mem_univ t⟩)
  have hvar := hdb.clm_apply hU.uniqueDiffOn hs.le hD (div_nonneg hC (sq_nonneg s)) hds
    ((variationLowJet_smooth hH).contDiffOn.prodMk contDiffOn_const) hpair
  convert hvar using 1
  ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
