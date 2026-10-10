import OAI.Geometry.SurfaceImmersion.Atlas.WeightedActualJets
import OAI.Geometry.SurfaceImmersion.Correction.HigherJetPolynomial

namespace OAI

/-! Uniform angular-slice estimates for smooth low-jet coefficients on a
compact admissible set. The angular parameter adds no scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_lowJet_pair {U : Set Base} (hU : IsOpen U) {Q : Base → LowJet}
    (hQ : ContDiffOn ℝ ∞ Q U) {s B : ℝ} (hs : 0 < s) (hB : 1 ≤ B) (m : ℕ)
    (hb : WeightedBound U s m B Q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    WeightedBound U s m (2 * B) (fun p => (Q p, t)) := by
  have hleft : WeightedBound U s m B (fun p => (Q p, (0 : ℝ))) := by
    simpa only [ContinuousLinearMap.norm_inl, one_mul, Function.comp_def,
      ContinuousLinearMap.inl_apply] using
      hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hc : ‖((0 : LowJet), t)‖ ≤ 1 := by
    rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg ht.1]
    exact max_le (by norm_num) ht.2
  have hright : WeightedBound U s m 1 (fun _ : Base => ((0 : LowJet), t)) :=
    (weightedBound_const U s m ((0 : LowJet), t)).mono_const hc
  have hsum := hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const) contDiffOn_const hright
  have hp : WeightedBound U s m (B + 1) (fun p => (Q p, t)) := by
    simpa only [Prod.mk_add_mk, add_zero, zero_add] using hsum
  exact hp.mono_const (by linarith)

/-- The same constant controls every angular slice over the unit period. -/
theorem compact_low_coefficient {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {c : LowJet × ℝ → ℝ} (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ))
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q : Base → LowJet) (s : ℝ), 0 < s →
      ContDiffOn ℝ ∞ Q U → Set.MapsTo Q U K → WeightedBound U s m B Q →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s m D (fun p => c (Q p, t)) := by
  have hcompact : IsCompact (K ×ˢ Set.Icc (0 : ℝ) 1) := hK.prod isCompact_Icc
  have hsub : K ×ˢ Set.Icc (0 : ℝ) 1 ⊆ O ×ˢ Set.univ :=
    fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
  obtain ⟨D, hD, hb⟩ := smooth_compact_weighted_bound hU.uniqueDiffOn
    (hO.prod isOpen_univ).uniqueDiffOn hcompact hsub hc m
  refine ⟨(m.factorial : ℝ) * D * (2 * B) ^ m, by positivity, ?_⟩
  intro Q s hs hQ hQK hQB t ht
  exact hb (fun p => (Q p, t)) s (2 * B) hs (by linarith)
    (hQ.prodMk contDiffOn_const) (fun p hp => ⟨hQK hp, ht⟩)
    (weighted_lowJet_pair hU hQ hs hB m hQB ht)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
