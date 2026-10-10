import OAI.Geometry.SurfaceImmersion.Correction.PolynomialTaylorBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationCalculus

namespace OAI

/-! The finite polynomial perturbation has a cubic nonlinear remainder with
one fixed scale loss. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ParameterTaylor WeightedEstimates

variable {n : ℕ}

def taylorRemainder (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space) (θ : ℝ) : Base → ℝ :=
  fun p => ∑ l, ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p

lemma taylorRemainder_identity (P : Fin n → Expression) (ε : ℝ) (G H : Base → Space)
    (θ : ℝ) (p : Base) :
    taylorRemainder P ε G H θ p =
      eval P ε (fun q => G q + H q) (p, θ) - eval P ε G (p, θ) - variation P ε G H (p, θ) -
        (1 / 2 : ℝ) * ∑ l, ε ^ (l.val + 1) * ((P l).variations 1).eval (diagonalFamily G H) (p, θ) := by
  simp only [taylorRemainder, Expression.taylorRemainder, eval, variation, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma expression_taylorRemainder_smooth {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    ContDiff ℝ ∞ (e.taylorRemainder G H θ) := by
  rw [← Expression.cubicRemainder_affine he hG hH θ]
  exact cubicRemainder_smooth (Expression.affinePolynomial_smooth he hG hH θ)

theorem compact_taylorRemainder_bound {U : Set Base} {Q : Set LowJet}
    (hU : IsOpen U) (hQ : IsCompact Q) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs Set.univ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G H : Base → Space) (s C ε : ℝ),
      0 < s → s ≤ 1 → 0 < C → 0 ≤ ε → ε ≤ 1 → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U s (m + order P) B
        (lowJet (fun p => G p + t • H p))) →
      WeightedBound U s (m + order P) C H →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        WeightedBound U s m (D * ε * C ^ 3 / s ^ loss P) (taylorRemainder P ε G H θ) := by
  classical
  have hex := fun l => (P l).compact_taylorRemainder_bound hU hQ (hP l) m B hB
  choose D hD hd using hex
  refine ⟨∑ l, D l / 2, Finset.sum_nonneg (fun l _ => div_nonneg (hD l) (by norm_num)), ?_⟩
  intro G H s C ε hs hs1 hC hε hε1 hG hH hGQ hGb hHb θ hθ
  have hval (l : Fin n) : WeightedBound U s m (D l / 2 * ε * C ^ 3 / s ^ loss P)
      (fun p => ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p) := by
    have hDl := hD l
    have hl : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hp := hd l G H s C hs hs1 hC hG hH hGQ
      (fun t ht => (hGb t ht).mono_order (Nat.add_le_add_left hl m))
      (hHb.mono_order (Nat.add_le_add_left hl m)) θ hθ
    have hp' : WeightedBound U s m (D l / 2 * C ^ 3 / s ^ loss P)
        ((P l).taylorRemainder G H θ) := by
      apply hp.mono_const
      have hpow := pow_le_pow_of_le_one hs.le hs1
        (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))
      calc
        _ = (D l / 2 * C ^ 3) / s ^ ((P l).loss + 6) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hs _) hpow
    have hsm := expression_taylorRemainder_smooth (hP l) hG hH θ
    have hscaled := hp'.const_smul hU.uniqueDiffOn hsm.contDiffOn (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have hpow : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l / 2 * C ^ 3 / s ^ loss P) := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = _ := by ring
  have hsum := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l / 2 * ε * C ^ 3 / s ^ loss P)
    (fun l p => ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p)
    (fun l _ => (contDiffOn_const.mul
      (expression_taylorRemainder_smooth (hP l) hG hH θ).contDiffOn)) (fun l _ => hval l)
  change WeightedBound U s m ((∑ l, D l / 2) * ε * C ^ 3 / s ^ loss P)
    (fun p => ∑ l, ε ^ (l.val + 1) * (P l).taylorRemainder G H θ p)
  simpa only [← Finset.sum_div, ← Finset.sum_mul] using hsum

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
