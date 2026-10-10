import OAI.Geometry.SurfaceImmersion.Correction.PolynomialVariationScaling

namespace OAI

/-! Product bounds for non-normalized variation maps. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression WeightedEstimates

namespace MixedExpression

lemma rescale_succ (G : Fin 4 → Base → Space) (c : Fin 3 → ℝ) (i : Fin 3) :
    rescale G c i.succ = fun p => c i • G i.succ p := by
  fin_cases i <;> rfl

lemma rescale_inverse (G : Fin 4 → Base → Space) (C : Fin 3 → ℝ)
    (hC : ∀ i, C i ≠ 0) : rescale (rescale G (fun i => (C i)⁻¹)) C = G := by
  funext i p
  fin_cases i <;> simp [rescale, smul_smul, hC]

end MixedExpression
namespace Expression

/-- Bounds for the first three actual variations, linear in each participating
map bound and with a single accuracy-independent scale exponent. -/
theorem compact_multilinear_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ) (C : Fin 3 → ℝ),
      0 < s → s ≤ 1 → (∀ i, 0 < C i) →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) (C i) (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) /
            s ^ (e.loss + 6)) (fun p => (e.variations i).eval G (p, t)) := by
  obtain ⟨D, hD, hb⟩ := e.compact_three_variation_bound hU hO hK hKO he m B hB
  refine ⟨D, hD, ?_⟩
  intro G s C hs hs1 hC hG hGK hGb hHb t ht i
  let H := rescale G (fun j => (C j)⁻¹)
  have hH := rescale_smooth hG (fun j => (C j)⁻¹)
  have hunit : ∀ j : Fin 3, WeightedBound U s (m + e.order) 1 (H j.succ) := by
    intro j
    have h := (hHb j).const_smul hU.uniqueDiffOn (hG j.succ).contDiffOn (C j)⁻¹
    simpa only [H, rescale_succ, abs_of_pos (inv_pos.mpr (hC j)),
      inv_mul_cancel₀ (ne_of_gt (hC j))] using h
  have hnorm := hb H s hs hs1 hH hGK hGb hunit t ht i
  let W : ℝ := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 < W := by
    have h₀ := hC 0
    have h₁ := hC 1
    have h₂ := hC 2
    dsimp only [W]
    split_ifs <;> positivity
  have heval : (fun p => (e.variations i).eval G (p, t)) =
      (fun p => W • (e.variations i).eval H (p, t)) := by
    funext p
    have hr := rescale_inverse G C (fun j => ne_of_gt (hC j))
    have hv := e.variations_rescale hH C (p, t) i
    rw [hr] at hv
    exact hv
  rw [heval]
  have hsmooth := MixedExpression.parameter_smooth hH
    (fun p hp => hKO (hGK hp)) (e := e.variations i) (e.variations_smoothCoeffs hO he i) t
  have h := hnorm.const_smul hU.uniqueDiffOn hsmooth W
  convert h using 1
  rw [abs_of_pos hW]
  ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
