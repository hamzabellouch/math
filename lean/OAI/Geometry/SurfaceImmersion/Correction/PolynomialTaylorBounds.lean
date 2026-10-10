import OAI.Geometry.SurfaceImmersion.Correction.PolynomialTaylorRemainder
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedMultilinearVariations

namespace OAI

/-! A fixed-power cubic remainder bound for the actual polynomial map. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open MixedExpression ParameterTaylor SmoothParameterIntegral WeightedEstimates

/-- The third variation controls the nonlinear remainder, with an exponent
independent of the requested output derivative order. -/
theorem compact_taylorRemainder_bound {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q) (e : Expression) (he : e.SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G H : Base → Space) (s C : ℝ),
      0 < s → s ≤ 1 → 0 < C → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + e.order) B
        (lowJet (fun p => G p + t • H p))) →
      WeightedBound U s (m + e.order) C H →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D * C ^ 3 / s ^ (e.loss + 6) / 2) (e.taylorRemainder G H θ) := by
  obtain ⟨D, hD, hd⟩ := e.compact_multilinear_variation_bound hU isOpen_univ hQ
    (Set.subset_univ Q) he m B hB
  refine ⟨D, hD, ?_⟩
  intro G H s C hs hs1 hC hG hH hGQ hGb hHb θ hθ
  apply weighted_taylorRemainder he hG hH θ hU hs
    (show 0 ≤ D * C ^ 3 / s ^ (e.loss + 6) by positivity) m
  intro j hj p hp t ht
  let V := varyBase (diagonalFamily G H) H t
  have hV : ∀ i, ContDiff ℝ ∞ (V i) :=
    varyBase_smooth (diagonalFamily_smooth hG hH) hH t
  have hVQ : Set.MapsTo (lowJet (V 0)) U Q := hGQ t ht
  have hVb : WeightedBound U s (m + e.order) B (lowJet (V 0)) := hGb t ht
  have hdirs : ∀ i : Fin 3, WeightedBound U s (m + e.order) C (V i.succ) := by
    intro i
    simpa only [V, varyBase_other _ _ _ (Fin.succ_ne_zero i), diagonalFamily_succ] using hHb
  have hv := hd V s (fun _ => C) hs hs1 (fun _ => hC) hV hVQ hVb hdirs θ hθ 2
  change WeightedBound U s m (D * (C * C * C) / s ^ (e.loss + 6))
    (fun p => (e.variations 2).eval V (p, θ)) at hv
  have hcubic : D * (C * C * C) / s ^ (e.loss + 6) = D * C ^ 3 / s ^ (e.loss + 6) := by ring
  rw [hcubic] at hv
  have hval := hv j hj p hp
  have hJ := eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH
    (e.variations_smoothCoeffs isOpen_univ he 2) θ
  have hslice := hJ.comp (contDiff_id.prodMk (contDiff_const (c := t)))
  change ContDiff ℝ ∞ (fun p => (e.variations 2).eval V (p, θ)) at hslice
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    ((hslice.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp] at hval
  exact hval

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
