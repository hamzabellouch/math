import OAI.Geometry.SurfaceImmersion.Geometry.ComplexMixedJets
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedCoefficientVariation

namespace OAI

/-! Two-scale evaluation: the output is measured at the slow scale, while
only the explicit jet excess contributes short-scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

def slotLoss (i : Fin 4) (w : List (Fin 2)) : ℕ :=
  if i = 0 then w.length - 2 else w.length

theorem compact_complex_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (J : JetData) (s τ : ℝ),
      0 < s → 0 < τ → τ ≤ 1 → ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U K →
      WeightedBound U s m B (lowJet G) →
      (∀ i w a, ContDiffOn ℝ ∞ (J i w a) U) →
      (∀ i w a, w.length ≤ e.order →
        WeightedBound U s m (B / τ ^ slotLoss i w) (J i w a)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / τ ^ e.loss) (fun p => e.evalComplex G J (p, t)) := by
  induction e with
  | coeff c =>
    have hc := Complex.ofRealCLM.contDiff.comp_contDiffOn he
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient_vector hU hO hK hKO hc m B hB
    refine ⟨D, hD, ?_⟩
    intro G J s τ hs _ _ hG hGK hb _ _ t ht
    simpa only [loss, pow_zero, div_one, evalComplex, Function.comp_def,
      Complex.ofRealCLM_apply] using hd (lowJet G) s hs (lowJet_smooth hG).contDiffOn hGK hb t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have htBound := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun j v b hv => hJB j v b (hv.trans (le_max_right _ _))) t ht
    have hjBound := hJB i w a (le_max_left _ _)
    have hp := hjBound.mul hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (hJ i w a) (evalComplex_parameter_smooth hG hQ hJ (e := e) he t) htBound
    convert hp using 1 <;> first | rfl | simp only [loss, slotLoss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G J s τ hs hτ hτ1 hG hGK hb hJ hJB t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_left _ _))) t ht
    have hc' := hc G J s τ hs hτ hτ1 hG hGK hb hJ
      (fun i w a hw => hJB i w a (hw.trans (le_max_right _ _))) t ht
    have hd'' : WeightedBound U s m (D / τ ^ max e.loss f.loss)
        (fun p => e.evalComplex G J (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / τ ^ max e.loss f.loss)
        (fun p => f.evalComplex G J (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hτ _)
        (pow_le_pow_of_le_one hτ.le hτ1 (le_max_right _ _)))
    simpa only [loss, add_div, evalComplex] using hd''.add hU.uniqueDiffOn hs.le
      (evalComplex_parameter_smooth hG hQ hJ (e := e) he.1 t)
      (evalComplex_parameter_smooth hG hQ hJ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
