import OAI.Geometry.SurfaceImmersion.Atlas.WeightedMixedJets
import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetDerivatives
import OAI.Geometry.SurfaceImmersion.Geometry.MixedJetHomogeneity

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

def variations (e : Expression) : Fin 3 → MixedExpression :=
  ![(ofExpression e).differentiate 0,
    ((ofExpression e).differentiate 0).differentiate 1,
    (((ofExpression e).differentiate 0).differentiate 1).differentiate 2]

lemma variations_smoothCoeffs {O : Set LowJet} (hO : IsOpen O)
    {e : Expression} (he : e.SmoothCoeffs O) (i : Fin 3) :
    (e.variations i).SmoothCoeffs O := by
  have h₀ := smoothCoeffs_ofExpression he
  have h₁ := differentiate_smoothCoeffs hO 0 h₀
  have h₂ := differentiate_smoothCoeffs hO 1 h₁
  have h₃ := differentiate_smoothCoeffs hO 2 h₂
  fin_cases i
  · exact h₁
  · exact h₂
  · exact h₃

lemma variations_order (e : Expression) (i : Fin 3) : (e.variations i).order ≤ e.order := by
  have h₁ := order_differentiate 0 (ofExpression e)
  have h₂ := order_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := order_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [order_ofExpression] at h₁
  fin_cases i
  · exact h₁
  · exact h₂.trans h₁
  · exact h₃.trans (h₂.trans h₁)

lemma variations_loss (e : Expression) (i : Fin 3) : (e.variations i).loss ≤ e.loss + 6 := by
  have h₁ := loss_differentiate 0 (ofExpression e)
  have h₂ := loss_differentiate 1 ((ofExpression e).differentiate 0)
  have h₃ := loss_differentiate 2 (((ofExpression e).differentiate 0).differentiate 1)
  rw [ofExpression_loss] at h₁
  fin_cases i
  · change ((ofExpression e).differentiate 0).loss ≤ e.loss + 6
    omega
  · change (((ofExpression e).differentiate 0).differentiate 1).loss ≤ e.loss + 6
    omega
  · exact loss_third_variation e

lemma first_variation_eval {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (z : Base × ℝ) (hQ : lowJet (G 0) z.1 ∈ O) :
    (e.variations 0).eval G z = e.variation (G 0) (G 1) z := by
  have ha := differentiate_hasDerivAt hO hG (smoothCoeffs_ofExpression he) 0 z hQ
  have hb := variation_hasDerivAt hO (hG 0) (hG 1) he z hQ
  have ha' : HasDerivAt (fun s : ℝ => e.eval (fun p => G 0 p + s • G 1 p) z)
      ((e.variations 0).eval G z) 0 := by
    change HasDerivAt _ (((ofExpression e).differentiate 0).eval G z) 0
    simpa only [ofExpression_eval, varyBase_base, Fin.succ_zero_eq_one] using ha
  exact ha'.unique hb

/-- The constant can depend on the requested output order; the exponent and
finite input loss do not. All three direction maps have unit weighted norm. -/
theorem compact_three_variation_bound {U : Set Base} {O K : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s : ℝ), 0 < s → s ≤ 1 →
      (∀ i, ContDiff ℝ ∞ (G i)) → Set.MapsTo (lowJet (G 0)) U K →
      WeightedBound U s (m + e.order) B (lowJet (G 0)) →
      (∀ i : Fin 3, WeightedBound U s (m + e.order) 1 (G i.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m (D / s ^ (e.loss + 6))
          (fun p => (e.variations i).eval G (p, t)) := by
  classical
  have hex := fun i : Fin 3 => compact_mixed_bound hU hO hK hKO (e.variations i)
    (e.variations_smoothCoeffs hO he i) m B hB
  choose D hD hb using hex
  refine ⟨∑ i, D i, Finset.sum_nonneg (fun i _ => hD i), ?_⟩
  intro G s hs hs1 hG hGK hGb hHb t ht i
  have hi := hb i G s hs hs1 hG hGK
    (hGb.mono_order (Nat.add_le_add_left (e.variations_order i) m))
    (fun j => (hHb j).mono_order (Nat.add_le_add_left (e.variations_order i) m)) t ht
  apply hi.mono_const
  calc
    D i / s ^ (e.variations i).loss ≤ D i / s ^ (e.loss + 6) :=
      div_le_div_of_nonneg_left (hD i) (pow_pos hs _)
        (pow_le_pow_of_le_one hs.le hs1 (e.variations_loss i))
    _ ≤ (∑ j, D j) / s ^ (e.loss + 6) :=
      div_le_div_of_nonneg_right (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))
        (pow_nonneg hs.le _)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
