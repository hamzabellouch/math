import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetRegularity
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialVariation

namespace OAI

/-! Uniform mixed-variation bounds with the sharp excess-jet scale loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression
open WeightedEstimates

/-- Unit weighted bounds on the direction maps cost their full jet orders;
the base map costs only the order beyond its controlled second jet. -/
theorem compact_mixed_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : MixedExpression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) 1 (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D / s ^ e.loss) (fun p => e.eval G (p, t)) := by
  induction e with
  | coeff c =>
    obtain ⟨D, hD, hd⟩ := compact_low_coefficient hU hO hK hKO he m B hB
    refine ⟨D, hD, ?_⟩
    intro G s hs _ hG hGK hb _ t ht
    simpa only [loss, pow_zero, div_one, eval] using
      hd (lowJet (G 0)) s hs (lowJet_smooth (hG 0)).contDiffOn hGK
        (hb.mono_order (by omega)) t ht
  | atom i w a e ih =>
    obtain ⟨D, hD, hd⟩ := ih he
    refine ⟨2 ^ m * B * D, by positivity, ?_⟩
    intro G s hs hs1 hG hGK hb hv t ht
    have hQ : Set.MapsTo (lowJet (G 0)) U O := fun _ hp => hKO (hGK hp)
    have htail := hd G s hs hs1 hG hGK
      (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hj : WeightedBound U s m
        (B / s ^ (if i = 0 then w.length - 2 else w.length)) (jet (G i) w a) := by
      by_cases hi : i = 0
      · subst i
        simp only [↓reduceIte]
        exact weighted_actual_jet hU (hG 0) hs (zero_le_one.trans hB) m w a
          (hb.mono_order (by simp only [order]; omega))
      · let j : Fin 3 := i.pred hi
        have hij : i = j.succ := (Fin.succ_pred i hi).symm
        rw [hij]
        simp only [Fin.succ_ne_zero, ↓reduceIte]
        exact (weighted_plain_jet hU (hG j.succ) hs zero_le_one m w a
          ((hv j).mono_order (by simp only [order]; omega))).mono_const
            (div_le_div_of_nonneg_right hB (pow_nonneg hs.le _))
    have hp := hj.mul_real hU.uniqueDiffOn hs.le (by positivity) (by positivity)
      (jet_smooth (hG i) w a).contDiffOn (parameter_smooth hG hQ (e := e) he t) htail
    convert hp using 1 <;> first | rfl | simp only [loss, pow_add]; ring
  | add e f ihe ihf =>
    obtain ⟨D, hD, hd⟩ := ihe he.1
    obtain ⟨C, hC, hc⟩ := ihf he.2
    refine ⟨D + C, add_nonneg hD hC, ?_⟩
    intro G s hs hs1 hG hGK hb hv t ht
    have hQ : Set.MapsTo (lowJet (G 0)) U O := fun _ hp => hKO (hGK hp)
    have hd' := hd G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hc' := hc G s hs hs1 hG hGK (hb.mono_order (by simp only [order]; omega))
      (fun j => (hv j).mono_order (by simp only [order]; omega)) t ht
    have hd'' : WeightedBound U s m (D / s ^ max e.loss f.loss) (fun p => e.eval G (p, t)) :=
      hd'.mono_const (div_le_div_of_nonneg_left hD (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_left _ _)))
    have hc'' : WeightedBound U s m (C / s ^ max e.loss f.loss) (fun p => f.eval G (p, t)) :=
      hc'.mono_const (div_le_div_of_nonneg_left hC (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (le_max_right _ _)))
    simpa only [loss, add_div, eval] using hd''.add hU.uniqueDiffOn hs.le
      (parameter_smooth hG hQ (e := e) he.1 t) (parameter_smooth hG hQ (e := f) he.2 t) hc''

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
