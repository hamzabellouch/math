import OAI.Geometry.SurfaceImmersion.Atlas.WeightedLowCoefficients
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialAlgebra

namespace OAI

/-! Uniform weighted estimates for actual coordinate-jet expressions.
The scale exponent is the algebraic excess-jet loss and is independent of
the requested output derivative order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

lemma parameter_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    {e : Expression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

/-- Compact low-jet control bounds every finite correction expression.
Only the numerical prefactor depends on the output derivative order. -/
theorem compact_expression_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) U K →
      WeightedBound U s (m + e.order) B (lowJet G) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / s ^ e.loss) (fun p => e.eval G (p, t)) := by
  induction e with
  | coeff c =>
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient hU hO hK hKO he m B hB
    refine ⟨D, hD, ?_⟩
    intro G s hs _ hG hGK hb t ht
    simpa only [loss, pow_zero, div_one, eval] using
      hd (lowJet G) s hs (lowJet_smooth hG).contDiffOn hGK (hb.mono_order (by omega)) t ht
  | atom w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G s hs hs1 hG hGK hb t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hj := weighted_actual_jet hU hG hs (zero_le_one.trans hB) m w a
      (hb.mono_order (by simp only [order]; omega))
    have hb' := hd G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega)) t ht
    have hp := hj.mul_real hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (jet_smooth hG w a).contDiffOn (parameter_smooth hG hQ (e := e) he t) hb'
    convert hp using 1 <;> first | rfl | simp only [loss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G s hs hs1 hG hGK hb t ht
    have hQ : Set.MapsTo (lowJet G) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega)) t ht
    have hc' := hc G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega)) t ht
    have hd'' : WeightedBound U s m (D / s ^ max e.loss f.loss) (fun p => e.eval G (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / s ^ max e.loss f.loss) (fun p => f.eval G (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_right _ _)))
    simpa only [loss, add_div, eval] using hd''.add hU.uniqueDiffOn hs.le
      (parameter_smooth hG hQ (e := e) he.1 t) (parameter_smooth hG hQ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
