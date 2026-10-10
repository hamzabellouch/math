import OAI.NumberTheory.TwoPoint.Bounds.ResidueExpansion
import OAI.NumberTheory.TwoPoint.AffineDeduction

namespace OAI

/-!
# From binary cancellation to every progression and affine forms

The character expansion treats all residue classes, while
finite-prime stability preserves nonpretentiousness of an original factor.
-/

open Filter
open scoped BigOperators ComplexConjugate

namespace TwoPointCorrelations

/-- The progression sum is a fixed finite linear combination of ordinary
binary sums, with no coprimality condition on the residue class. -/
theorem residuePrefix_eq_component_correlations (f g : ℕ → ℂ) (h l b N : ℕ)
    (hl : 0 < l) :
    residuePrefix (fun n => f n * g (n + h)) l b N =
      ((l / b.gcd l).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
          ∑ E ∈ (b.gcd l).primeFactors.powerset,
            (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
              correlationSum (residueComponent f (b.gcd l) χ E) g 0 h N := by
  have hI : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  unfold residuePrefix
  calc
    _ = ∑ n ∈ Finset.Ioc 0 N,
        ((l / b.gcd l).totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ (l / b.gcd l),
            ∑ E ∈ (b.gcd l).primeFactors.powerset,
              (conj (naturalCharacter χ (b / b.gcd l)) * (-1 : ℂ) ^ E.card) *
                (residueComponent f (b.gcd l) χ E n * g (n + h)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos := (Finset.mem_Ioc.mp hn).1
      rw [show (if n % l = b % l then f n * g (n + h) else 0) =
          (if n % l = b % l then f n else 0) * g (n + h) by split_ifs <;> simp]
      rw [residue_weight_eq_components f l b n hl hnpos, mul_assoc]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro E _
      rw [← Finset.mul_sum]
      simp only [correlationSum, hI, Nat.add_zero]

/-- Every-residue progression cancellation follows from the
binary corrected Elliott statement by finite character expansion. -/
theorem BinaryCorrectedElliott.progression (hbinary : BinaryCorrectedElliott) :
    ProgressionCorrectedElliott := by
  intro f g hf hg hfb hgb hnp h l b hh hl
  let d := b.gcd l
  let q := l / d
  let c := b / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right b hl
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hl (Nat.gcd_dvd_right b l)) hd
  have hpiece (χ : DirichletCharacter ℂ q) (E : Finset ℕ) :
      Tendsto (fun N : ℕ => correlationSum (residueComponent f d χ E) g 0 h N /
        (N : ℂ)) atTop (nhds 0) := by
    apply hbinary _ _ (residueComponent_multiplicative f d χ E hf) hg
      (residueComponent_oneBounded f d χ E hfb) hgb _ 0 h hh.ne
    exact hnp.imp (residueComponent_nonpretentious f d χ E hq hfb) id
  have hsum := tendsto_finsetSum (Finset.univ : Finset (DirichletCharacter ℂ q))
    (fun χ _ => tendsto_finsetSum d.primeFactors.powerset (fun E _ =>
      (tendsto_const_nhds (x := conj (naturalCharacter χ c) * (-1 : ℂ) ^ E.card)).mul
        (hpiece χ E)))
  have hlimit := (tendsto_const_nhds (x := (q.totient : ℂ)⁻¹)).mul hsum
  have heq (N : ℕ) :
      residuePrefix (fun n => f n * g (n + h)) l b N / (N : ℂ) =
        (q.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, ∑ E ∈ d.primeFactors.powerset,
            (conj (naturalCharacter χ c) * (-1 : ℂ) ^ E.card) *
              (correlationSum (residueComponent f d χ E) g 0 h N / (N : ℂ)) := by
    rw [residuePrefix_eq_component_correlations f g h l b N hl]
    simp only [d, q, c, mul_div_assoc, Finset.sum_div]
  simp_rw [heq]
  simpa using hlimit

/-- The complete qualitative affine reduction, including nonunit slopes and
either original nonpretentious factor, assuming binary cancellation. -/
theorem BinaryCorrectedElliott.affine (hbinary : BinaryCorrectedElliott) :
    AffineCorrectedElliott := hbinary.progression.affine

end TwoPointCorrelations

end OAI
