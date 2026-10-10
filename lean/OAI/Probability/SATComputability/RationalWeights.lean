import OAI.Probability.DilutedSpin.FiniteLaw

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass
open scoped BigOperators

def RationalWeights (ι : Type*) [Fintype ι] :=
  {w : ι → ℚ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

noncomputable def RationalWeights.toLaw {ι : Type*} [Fintype ι]
    (w : RationalWeights ι) : FiniteLaw ι where
  weight i := w.val i
  nonneg i := by exact_mod_cast w.property.1 i
  total := by exact_mod_cast w.property.2

abbrev ProbabilityVector (ι : Type*) [Fintype ι] :=
  {w : ι → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

noncomputable def RationalWeights.real {ι : Type*} [Fintype ι]
    (w : RationalWeights ι) : ProbabilityVector ι :=
  ⟨w.toLaw.weight, w.toLaw.nonneg, w.toLaw.total⟩

theorem exists_rational_weights_near {ι : Type*} [Fintype ι]
    (w : FiniteLaw ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : RationalWeights ι, ∀ i, |(q.val i : ℝ) - w.weight i| < ε := by
  classical
  let δ := ε / (2 * (Fintype.card ι + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : (Fintype.card ι + 1 : ℝ) * δ < ε := by
    dsimp [δ]
    have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
    field_simp
    linarith
  have hex (i : ι) : ∃ q : ℚ, w.weight i < q ∧ (q : ℝ) < w.weight i + δ :=
    exists_rat_btwn (by linarith)
  choose v hv using hex
  let S : ℚ := ∑ i, v i
  have hSreal : (S : ℝ) = ∑ i, (v i : ℝ) := by simp [S]
  have hS : 1 ≤ (S : ℝ) := by
    rw [hSreal, ← w.total]
    exact Finset.sum_le_sum (fun i _ => (hv i).1.le)
  have hSupper : (S : ℝ) ≤ 1 + Fintype.card ι * δ := by
    calc
      (S : ℝ) = ∑ i, (v i : ℝ) := hSreal
      _ ≤ ∑ i, (w.weight i + δ) := Finset.sum_le_sum (fun i _ => (hv i).2.le)
      _ = _ := by simp [Finset.sum_add_distrib, w.total]
  have hSpos : 0 < S := by exact_mod_cast (show (0 : ℝ) < S by linarith)
  let q : RationalWeights ι := ⟨fun i => v i / S, by
    constructor
    · intro i
      have hv0 : 0 ≤ v i := by exact_mod_cast ((w.nonneg i).trans (hv i).1.le)
      exact div_nonneg hv0 hSpos.le
    · rw [← Finset.sum_div]
      exact div_self hSpos.ne'⟩
  refine ⟨q, fun i => ?_⟩
  have hwi : w.weight i ≤ 1 := by
    rw [← w.total]
    exact Finset.single_le_sum (fun j _ => w.nonneg j) (Finset.mem_univ i)
  have hvi := hv i
  have hw0 := w.nonneg i
  have hs0 : 0 < (S : ℝ) := by linarith
  have hδsmall : δ < ε := by
    have hn : (1 : ℝ) ≤ Fintype.card ι + 1 := by
      linarith [show (0 : ℝ) ≤ Fintype.card ι from Nat.cast_nonneg _]
    nlinarith
  have hnsmall : (Fintype.card ι : ℝ) * δ < ε := by linarith
  have hprod := mul_le_mul_of_nonneg_left hSupper hw0
  have hcard := mul_le_mul_of_nonneg_right hwi
    (show 0 ≤ (Fintype.card ι : ℝ) * δ by positivity)
  have heps := mul_le_mul_of_nonneg_left hS hε.le
  have hws := mul_le_mul_of_nonneg_left hS hw0
  change |((v i / S : ℚ) : ℝ) - w.weight i| < ε
  rw [Rat.cast_div, abs_lt]
  constructor
  · have : w.weight i - ε < (v i : ℝ) / S := by
      apply (lt_div_iff₀ hs0).mpr
      nlinarith
    linarith
  · have : (v i : ℝ) / S < w.weight i + ε := by
      apply (div_lt_iff₀ hs0).mpr
      nlinarith
    linarith

theorem rationalWeights_dense {ι : Type*} [Fintype ι] :
    DenseRange (RationalWeights.real (ι := ι)) := by
  intro w
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let P : FiniteLaw ι := ⟨w.val, w.property.1, w.property.2⟩
  obtain ⟨q, hq⟩ := exists_rational_weights_near P hε
  refine ⟨q.real, ⟨q, rfl⟩, ?_⟩
  rw [dist_comm]
  change dist (fun i => (q.val i : ℝ)) w.val < ε
  apply (dist_pi_lt_iff hε).mpr
  intro i
  simpa only [Real.dist_eq] using hq i

end FixedClauseThreshold.Computability

end OAI
