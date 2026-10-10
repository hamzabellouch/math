import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockEliminationSchedule
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-!
# Scalar diagonal representatives transverse to the root blocks

After clearing the within-block off-diagonal entries, a positive split
diagonal makes all diagonal entries equal. Both corrections belong to
the actual invariant subgroup when it contains A and the specified
roots. Thus this normalization preserves being outside that subgroup.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def balancedDiagonalMean {n : ℕ} (g : G n) : ℝ :=
  (∑ i, Real.log (g.val i i)) / n

def balancedDiagonalWeights {n : ℕ} (g : G n) (i : Fin n) : ℝ :=
  balancedDiagonalMean g - Real.log (g.val i i)

lemma balancedDiagonalWeights_sum {n : ℕ} (hn : n ≠ 0) (g : G n) :
    ∑ i, balancedDiagonalWeights g i = 0 := by
  simp only [balancedDiagonalWeights, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, balancedDiagonalMean]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn]
  ring

def balancedDiagonalCorrection {n : ℕ} (hn : n ≠ 0) (g : G n) : G n :=
  diagonalOneParameter (balancedDiagonalWeights g) (balancedDiagonalWeights_sum hn g) 1

lemma balancedDiagonalCorrection_entry {n : ℕ} (hn : n ≠ 0)
    (g : G n) (i j : Fin n) :
    (g * balancedDiagonalCorrection hn g).val i j =
      g.val i j * Real.exp (balancedDiagonalWeights g j) := by
  change (g.val * Matrix.diagonal (fun k =>
    Real.exp (balancedDiagonalWeights g k * 1))) i j = _
  simp only [Matrix.mul_diagonal, mul_one]

lemma balancedDiagonalCorrection_diagonal {n : ℕ} (hn : n ≠ 0)
    (g : G n) (hpos : ∀ i, 0 < g.val i i) (i : Fin n) :
    (g * balancedDiagonalCorrection hn g).val i i = Real.exp (balancedDiagonalMean g) := by
  rw [balancedDiagonalCorrection_entry, balancedDiagonalWeights, Real.exp_sub,
    Real.exp_log (hpos i)]
  field_simp [ne_of_gt (hpos i)]

lemma balancedDiagonalMean_tendsto {n : ℕ} (g : ℕ → G n)
    (hg : Tendsto g atTop (𝓝 1)) :
    Tendsto (fun k => balancedDiagonalMean (g k)) atTop (𝓝 0) := by
  have hi (i : Fin n) : Tendsto (fun k => Real.log ((g k).val i i)) atTop (𝓝 0) := by
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have he := hc.continuousAt.tendsto.comp hg
    have he' : Tendsto (fun k => (g k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using he
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp he'
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [balancedDiagonalMean, Finset.sum_const_zero, zero_div] using hs.div_const (n : ℝ)

lemma balancedDiagonalCorrection_tendsto {n : ℕ} (hn : n ≠ 0)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) :
    Tendsto (fun k => balancedDiagonalCorrection hn (g k)) atTop (𝓝 1) := by
  have hi (i : Fin n) : Tendsto (fun k => Real.log ((g k).val i i)) atTop (𝓝 0) := by
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have he := hc.continuousAt.tendsto.comp hg
    have he' : Tendsto (fun k => (g k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using he
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp he'
  have hw (i : Fin n) : Tendsto (fun k => balancedDiagonalWeights (g k) i)
      atTop (𝓝 0) := by
    simpa only [balancedDiagonalWeights, sub_zero] using
      (balancedDiagonalMean_tendsto g hg).sub (hi i)
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simp only [balancedDiagonalCorrection, diagonalOneParameter, Matrix.diagonal_apply_eq,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq, mul_one]
    simpa only [Function.comp_def, mul_one, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp (hw i)
  · change Tendsto (fun k => (Matrix.diagonal (fun a =>
      Real.exp (balancedDiagonalWeights (g k) a * 1))) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j))
    simpa only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Every small matrix has a representative with scalar diagonal and
zero within-block off-diagonal entries, using actual elements of L. -/
theorem exists_scalar_block_transverse_sequence {n : ℕ} (hn : n ≠ 0)
    (r : Setoid (Fin n)) (L : Subgroup (G n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), r i j → ∀ t : ℝ,
      Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hdiag : ∀ (ell : Fin n → ℝ) (hsum : ∑ i, ell i = 0) (t : ℝ),
      diagonalOneParameter ell hsum t ∈ L)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) :
    ∃ s b : ℕ → G n, ∃ c : ℕ → ℝ,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧ (∀ k, b k ∈ L) ∧
      (∀ k, 0 < c k) ∧
      ∀ᶠ k in atTop, (∀ i, (s k).val i i = c k) ∧
        ∀ i j, i ≠ j → r i j → (s k).val i j = 0 := by
  obtain ⟨u, b, hu, hb, he, hmem, hz⟩ := exists_block_transverse_sequence r g hg
  let a : ℕ → G n := fun k => balancedDiagonalCorrection hn (u k)
  let s : ℕ → G n := fun k => u k * a k
  let b' : ℕ → G n := fun k => b k * a k
  let c : ℕ → ℝ := fun k => Real.exp (balancedDiagonalMean (u k))
  have ha : Tendsto a atTop (𝓝 1) := balancedDiagonalCorrection_tendsto hn u hu
  have hle : blockRootGroup r ≤ L := by
    rw [blockRootGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, t, hr, rfl⟩
    exact hroot i j hij hr t
  have hpos : ∀ᶠ k in atTop, ∀ i, 0 < (u k).val i i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have hlim := hc.continuousAt.tendsto.comp hu
    have hlim' : Tendsto (fun k => (u k).val i i) atTop (𝓝 1) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] using hlim
    exact hlim'.eventually (lt_mem_nhds zero_lt_one)
  refine ⟨s, b', c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [s, mul_one] using hu.mul ha
  · simpa only [b', mul_one] using hb.mul ha
  · intro k
    dsimp only [s, b']
    rw [he k, mul_assoc]
  · intro k
    exact L.mul_mem (hle (hmem k))
      (hdiag _ (balancedDiagonalWeights_sum hn (u k)) 1)
  · exact fun k => Real.exp_pos _
  · filter_upwards [hpos, hz] with k hk hkz
    constructor
    · exact balancedDiagonalCorrection_diagonal hn (u k) hk
    · intro i j hij hr
      change (u k * balancedDiagonalCorrection hn (u k)).val i j = 0
      rw [balancedDiagonalCorrection_entry, hkz i j hij hr, zero_mul]

lemma right_corrected_not_mem {n : ℕ} (L : Subgroup (G n))
    {g b : G n} (hg : g ∉ L) (hb : b ∈ L) : g * b ∉ L := by
  intro h
  exact hg (by simpa only [mul_inv_cancel_right] using L.mul_mem h (L.inv_mem hb))

/-- A nonidentity scalar-diagonal representative must retain a genuine
cross-block entry; a positive scalar determinant-one matrix is identity. -/
theorem exists_cross_block_entry_of_scalar_diagonal {n : ℕ} (hn : n ≠ 0)
    (r : Setoid (Fin n)) (g : G n) (c : ℝ) (hc : 0 < c)
    (hdiag : ∀ i, g.val i i = c)
    (hwithin : ∀ i j, i ≠ j → r i j → g.val i j = 0)
    (hne : g ≠ 1) : ∃ i j, ¬ r i j ∧ g.val i j ≠ 0 := by
  by_contra h
  push Not at h
  have he : g.val = Matrix.diagonal (fun _ => c) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, hdiag]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hr : r i j
      · exact hwithin i j hij hr
      · exact h i j hr
  have hpow : c ^ n = 1 := by
    have hd := g.property
    rw [he, Matrix.det_diagonal] at hd
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hd
  have hc1 : c = 1 := (pow_eq_one_iff_of_nonneg hc.le hn).mp hpow
  apply hne
  apply Subtype.ext
  rw [he, hc1]
  simp

end DukePrimeDegree

end

end OAI
