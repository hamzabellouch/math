import OAI.Geometry.SurfaceImmersion.Correction.RealPolynomialVariationBounds

namespace OAI

/-! Bilinear bounds for the mixed polynomial contribution of the free and
forced displacements. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

def quadraticCross {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G H K : Base → Space) (t : ℝ) : Base → ℝ :=
  fun p => (1 / 2 : ℝ) * (realVariation P ε ![G,H,K,0] 1 t p +
    realVariation P ε ![G,K,H,0] 1 t p)

lemma pairFamily_smooth {G H K : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    ∀ i, ContDiff ℝ ∞ (![G,H,K,0] i) := by
  intro i
  fin_cases i
  · exact hG
  · exact hH
  · exact hK
  · exact contDiff_const

lemma realVariation_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Fin 4 → Base → Space} (hG : ∀ j, ContDiff ℝ ∞ (G j))
    (hQ : Set.MapsTo (lowJet (G 0)) U O) (ε : ℝ) (i : Fin 3) (t : ℝ) :
    ContDiffOn ℝ ∞ (realVariation P ε G i t) U :=
  ContDiffOn.sum fun l _ => contDiffOn_const.mul
    (MixedExpression.parameter_smooth hG hQ ((P l).variations_smoothCoeffs hO (hP l) i) t)

theorem quadraticCross_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (G H K : Base → Space) (s ε C D : ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → 0 < C → 0 < D →
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H → ContDiff ℝ ∞ K →
      Set.MapsTo (lowJet G) U Q → WeightedBound U s (m + order P) B (lowJet G) →
      WeightedBound U s (m + order P) C H → WeightedBound U s (m + order P) D K →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (E * ε * C * D / s ^ loss P) (quadraticCross P ε G H K t) := by
  obtain ⟨E,hE,he⟩ := compact_real_variation_bound hU hO hQ hQO P hP m B hB
  refine ⟨E,hE,?_⟩
  intro G H K s ε C D hs hs1 hε hε1 hC hD hG hH hK hGQ hGb hHb hKb t ht
  have hh (X Y : Base → Space) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
      (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
      (hbX : WeightedBound U s (m + order P) A X)
      (hbY : WeightedBound U s (m + order P) B Y) :
      WeightedBound U s m (E * ε * A * B / s ^ loss P) (realVariation P ε ![G,X,Y,0] 1 t) := by
    have hb : ∀ j : Fin 3, WeightedBound U s (m + order P) (![A,B,1] j) (![G,X,Y,0] j.succ) := by
      intro j
      fin_cases j
      · exact hbX
      · exact hbY
      · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
    have hx := he ![G,X,Y,0] s ε ![A,B,1] hs hs1 hε hε1
      (fun j => by fin_cases j; exact hA; exact hB; norm_num)
      (pairFamily_smooth hG hX hY) hGQ hGb hb t ht 1
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 3) ≤ 1 by decide,
      show ¬ (2 : Fin 3) ≤ 1 by decide, ↓reduceIte, mul_one, mul_assoc] using hx
  have hsHK := realVariation_smooth hO hP (pairFamily_smooth hG hH hK)
    (fun _ hp => hQO (hGQ hp)) ε 1 t
  have hsKH := realVariation_smooth hO hP (pairFamily_smooth hG hK hH)
    (fun _ hp => hQO (hGQ hp)) ε 1 t
  have hb := (hh H K C D hC hD hH hK hHb hKb).add hU.uniqueDiffOn hs.le hsHK hsKH
    (hh K H D C hD hC hK hH hKb hHb)
  have hf := hb.const_smul hU.uniqueDiffOn (hsHK.add hsKH) (1 / 2 : ℝ)
  change WeightedBound U s m _ (quadraticCross P ε G H K t) at hf
  convert hf using 1
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
