import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationBounds
import OAI.Geometry.SurfaceImmersion.Atlas.WeightedMultilinearVariations

namespace OAI

/-! Bounds for arbitrary real variations at the short scale. These are the
nonoscillatory estimates used for mixed terms and the Taylor remainder. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

def realVariation {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Fin 4 → Base → Space) (i : Fin 3) (t : ℝ) : Base → ℝ :=
  fun p => ∑ l, ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t)

theorem compact_real_variation_bound {n : ℕ} {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Fin 4 → Base → Space) (s ε : ℝ) (C : Fin 3 → ℝ),
      0 < s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 → (∀ j, 0 < C j) →
      (∀ j, ContDiff ℝ ∞ (G j)) → Set.MapsTo (lowJet (G 0)) U Q →
      WeightedBound U s (m + order P) B (lowJet (G 0)) →
      (∀ j : Fin 3, WeightedBound U s (m + order P) (C j) (G j.succ)) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 3,
        WeightedBound U s m
          (D * ε * (C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)) / s ^ loss P)
          (realVariation P ε G i t) := by
  have hex (l : Fin n) := (P l).compact_multilinear_variation_bound hU hO hQ hQO (hP l) m B hB
  choose D hD hd using hex
  refine ⟨∑ l, D l, Finset.sum_nonneg (fun l _ => hD l), ?_⟩
  intro G s ε C hs hs1 hε hε1 hC hG hGQ hGb hHb t ht i
  let W := C 0 * (if 1 ≤ i then C 1 else 1) * (if 2 ≤ i then C 2 else 1)
  have hW : 0 ≤ W := by
    have h0 := (hC 0).le
    have h1 := (hC 1).le
    have h2 := (hC 2).le
    dsimp only [W]
    split_ifs <;> positivity
  have hv (l : Fin n) : WeightedBound U s m (D l * ε * W / s ^ loss P)
      (fun p => ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t)) := by
    have hDl := hD l
    have ho : (P l).order ≤ order P := Finset.le_sup (f := fun k => (P k).order) (Finset.mem_univ l)
    have hh := hd l G s C hs hs1 hC hG hGQ
      (hGb.mono_order (Nat.add_le_add_left ho m))
      (fun j => (hHb j).mono_order (Nat.add_le_add_left ho m)) t ht i
    have hsmall := hh.mono_const (div_le_div_of_nonneg_left (mul_nonneg (hD l) hW) (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1
        (Finset.le_sup (f := fun k => (P k).loss + 6) (Finset.mem_univ l))))
    have hsm := MixedExpression.parameter_smooth hG (fun p hp => hQO (hGQ hp))
      (e := (P l).variations i) ((P l).variations_smoothCoeffs hO (hP l) i) t
    have hscaled := hsmall.const_smul hU.uniqueDiffOn hsm (ε ^ (l.val + 1))
    apply hscaled.mono_const
    rw [abs_of_nonneg (pow_nonneg hε _)]
    have he : ε ^ (l.val + 1) ≤ ε := by
      simpa only [pow_one] using pow_le_pow_of_le_one hε hε1 (show 1 ≤ l.val + 1 by omega)
    calc
      _ ≤ ε * (D l * W / s ^ loss P) := mul_le_mul_of_nonneg_right he (by positivity)
      _ = _ := by ring
  have hh := WeightedBound.finset_sum hU.uniqueDiffOn hs.le Finset.univ
    (fun l => D l * ε * W / s ^ loss P)
    (fun l p => ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t))
    (fun l _ => contDiffOn_const.mul (MixedExpression.parameter_smooth hG (fun p hp => hQO (hGQ hp))
      (e := (P l).variations i) ((P l).variations_smoothCoeffs hO (hP l) i) t))
    (fun l _ => hv l)
  change WeightedBound U s m ((∑ l, D l) * ε * W / s ^ loss P)
    (fun p => ∑ l, ε ^ (l.val + 1) * ((P l).variations i).eval G (p,t))
  simpa only [← Finset.sum_div, ← Finset.sum_mul] using hh

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
