import OAI.Geometry.SurfaceImmersion.Correction.WeightedJetExpressions

namespace OAI

/-! Two-scale estimates for the actual higher-jet expressions, with a varying
angular phase. The slow-jet loss is independent of the output derivative order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weighted_pair {U : Set Base} (hU : IsOpen U)
    {Q : Base → LowJet} {t : Base → ℝ} (hQ : ContDiffOn ℝ ∞ Q U)
    (ht : ContDiffOn ℝ ∞ t U) {s B P : ℝ} {m : ℕ} (hs : 0 < s)
    (hb : WeightedBound U s m B Q) (hp : WeightedBound U s m P t) :
    WeightedBound U s m (B + P) (fun p => (Q p, t p)) := by
  have hleft := hb.linear hU.uniqueDiffOn hs.le hQ (ContinuousLinearMap.inl ℝ LowJet ℝ)
  have hright := hp.linear hU.uniqueDiffOn hs.le ht (ContinuousLinearMap.inr ℝ LowJet ℝ)
  simp only [ContinuousLinearMap.norm_inl, ContinuousLinearMap.norm_inr, one_mul,
    Function.comp_def, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply] at hleft hright
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using
    hleft.add hU.uniqueDiffOn hs.le (hQ.prodMk contDiffOn_const)
      (contDiffOn_const.prodMk ht) hright

namespace Expression

lemma phase_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space} {t : Base → ℝ}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (ht : ContDiffOn ℝ ∞ t U) {e : Expression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t p)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk ht)
    (fun _ hp => ⟨hp, Set.mem_univ _⟩)

/-- The constant is uniform over the open spatial domain and the phase.
The two scales are kept separate: differentiation is weighted at `τ`, whereas
higher jets only cost powers of the slower scale `s`. -/
theorem compact_phase_bound {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ)
    (B P : ℝ) (hB : 1 ≤ B) (hP : 1 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set Base), IsOpen U →
      ∀ (G : Base → Space) (t : Base → ℝ) (s τ : ℝ),
      0 < τ → τ ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      ContDiffOn ℝ ∞ t U → Set.MapsTo (lowJet G) U K →
      Set.MapsTo t U (Set.Icc (-1) 2) →
      WeightedBound U s (m + e.order) B (lowJet G) →
      WeightedBound U τ m P t →
      WeightedBound U τ m (D / s ^ e.loss) (fun p => e.eval G (p, t p)) := by
  induction e with
  | coeff c =>
    have hcompact : IsCompact (K ×ˢ Set.Icc (-1 : ℝ) 2) := hK.prod isCompact_Icc
    have hsub : K ×ˢ Set.Icc (-1 : ℝ) 2 ⊆ O ×ˢ Set.univ :=
      fun _ hz => ⟨hKO hz.1, Set.mem_univ _⟩
    obtain ⟨D, hD, hd⟩ := compact_coefficient_bound
      (hO.prod isOpen_univ).uniqueDiffOn hcompact hsub he m
    refine ⟨(m.factorial : ℝ) * D * (B + P) ^ m, by positivity, ?_⟩
    intro U hU G t s τ hτ hτs _ hG ht hGK htk hb hp
    have hb' := (hb.mono_order (by simp [order] : m ≤ m + (Expression.coeff c).order)).shrink_scale hτ.le hτs
    have hpq := weighted_pair hU (lowJet_smooth hG).contDiffOn ht hτ hb' hp
    have hh := hpq.comp hU.uniqueDiffOn (hO.prod isOpen_univ).uniqueDiffOn
      hτ (by linarith : 1 ≤ B + P) (zero_le_one.trans hD)
      ((lowJet_smooth hG).contDiffOn.prodMk ht) he
      (fun x hx => ⟨hKO (hGK hx), Set.mem_univ _⟩)
      (fun j hj x hx => hd j hj _ ⟨hGK hx, htk hx⟩)
    simpa only [loss, pow_zero, div_one, eval, Function.comp_def] using hh
  | atom w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro U hU G t s τ hτ hτs hs1 hG ht hGK htk hb hp
    have hs : 0 < s := hτ.trans_le hτs
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hx => hKO (hGK hx)
    have hj := (weighted_actual_jet hU hG hs (zero_le_one.trans hB) m w a
      (hb.mono_order (by simp only [order]; omega))).shrink_scale hτ.le hτs
    have hb' := hd U hU G t s τ hτ hτs hs1 hG ht hGK htk
      (hb.mono_order (by simp only [order]; omega)) hp
    have hh := hj.mul_real hU.uniqueDiffOn hτ.le (by positivity) (by positivity)
      (jet_smooth hG w a).contDiffOn (phase_smooth hG hQ ht (e := e) he) hb'
    convert hh using 1 <;> first | rfl | simp only [loss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro U hU G t s τ hτ hτs hs1 hG ht hGK htk hb hp
    have hs : 0 < s := hτ.trans_le hτs
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hx => hKO (hGK hx)
    have hd' := hd U hU G t s τ hτ hτs hs1 hG ht hGK htk
      (hb.mono_order (by simp only [order]; omega)) hp
    have hc' := hc U hU G t s τ hτ hτs hs1 hG ht hGK htk
      (hb.mono_order (by simp only [order]; omega)) hp
    have hd'' : WeightedBound U τ m (D / s ^ max e.loss f.loss) (fun p => e.eval G (p, t p)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_left _ _)))
    have hc'' : WeightedBound U τ m (C / s ^ max e.loss f.loss) (fun p => f.eval G (p, t p)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_right _ _)))
    simpa only [loss, add_div, eval] using hd''.add hU.uniqueDiffOn hτ.le
      (phase_smooth hG hQ ht (e := e) he.1) (phase_smooth hG hQ ht (e := f) he.2) hc''

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
