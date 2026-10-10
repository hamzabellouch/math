import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockErgodicity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockTransverseDiagonal

namespace OAI

/-!
# Transverse representatives using only a single root block

On an ergodic component for a single root block, an arbitrary ambient
diagonal correction need not preserve the component measure.  Here the
correction is a product of roots in that block.  It clears the entries
inside the block and equalizes its diagonal, leaving the complementary
coordinates unrestricted.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

attribute [local irreducible] singleBlockRootGroup

def singleBlockSetoid {n : ℕ} (S : Set (Fin n)) : Setoid (Fin n) where
  r i j := i = j ∨ (i ∈ S ∧ j ∈ S)
  iseqv := ⟨fun _ => Or.inl rfl, by aesop, by aesop⟩

lemma singleBlockSetoid_off_diagonal {n : ℕ} (S : Set (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    singleBlockSetoid S i j ↔ i ∈ S ∧ j ∈ S := by
  change (i = j ∨ (i ∈ S ∧ j ∈ S)) ↔ _
  simp only [hij, false_or]

lemma blockRootGroup_singleBlockSetoid {n : ℕ} (S : Set (Fin n)) :
    blockRootGroup (singleBlockSetoid S) = singleBlockRootGroup S := by
  apply le_antisymm
  · rw [blockRootGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, t, hr, rfl⟩
    obtain ⟨hi, hj⟩ := (singleBlockSetoid_off_diagonal S hij).mp hr
    exact root_mem_singleBlockRootGroup S i hi j hj hij t
  · apply singleBlockRootGroup_le_of_roots
    intro i hi j hj hij t
    exact root_mem_blockRootGroup (singleBlockSetoid S) i j hij (Or.inr ⟨hi, hj⟩) t

/-- A diagonal supported on one coordinate block belongs to its actual
root-generated group, provided its determinant is one. -/
theorem supported_diagonal_mem_singleBlockRootGroup {n : ℕ}
    (S : Set (Fin n)) (i₀ : Fin n) (hi₀ : i₀ ∈ S)
    (D : Fin n → ℝ) (hdet : Matrix.det (Matrix.diagonal D) = 1)
    (hsupport : ∀ i, i ∉ S → D i = 1) :
    (⟨Matrix.diagonal D, hdet⟩ : G n) ∈ singleBlockRootGroup S := by
  rw [Matrix.SpecialLinearGroup.diag_eq_diag2n_prod i₀ D hdet]
  apply (singleBlockRootGroup S).noncommProd_mem
  intro i hi
  split_ifs with hii
  · by_cases hiS : i ∈ S
    · exact diag2n_mem_of_opposite_roots hii (singleBlockRootGroup S)
        (root_mem_singleBlockRootGroup S i hiS i₀ hi₀ hii)
        (root_mem_singleBlockRootGroup S i₀ hi₀ i hiS hii.symm)
        (D i) (Matrix.SpecialLinearGroup.diagonal_neZero D hdet i)
    · have he : Matrix.SpecialLinearGroup.diag2n hii (D i)
          (Matrix.SpecialLinearGroup.diagonal_neZero D hdet i) = 1 := by
        apply Subtype.ext
        ext a b
        simp [Matrix.SpecialLinearGroup.diag2n_coe, hsupport i hiS]
      rw [he]
      exact (singleBlockRootGroup S).one_mem
  · exact (singleBlockRootGroup S).one_mem

theorem supported_diagonalOneParameter_mem_singleBlockRootGroup {n : ℕ}
    (S : Set (Fin n)) (i₀ : Fin n) (hi₀ : i₀ ∈ S)
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (hsupport : ∀ i, i ∉ S → ell i = 0) (t : ℝ) :
    diagonalOneParameter ell hell t ∈ singleBlockRootGroup S := by
  apply supported_diagonal_mem_singleBlockRootGroup S i₀ hi₀
  intro i hi
  simp only [hsupport i hi, zero_mul, Real.exp_zero]

def singleBlockDiagonalMean {n : ℕ} (S : Finset (Fin n)) (g : G n) : ℝ :=
  (∑ i ∈ S, Real.log (g.val i i)) / S.card

def singleBlockDiagonalWeights {n : ℕ} (S : Finset (Fin n))
    (g : G n) (i : Fin n) : ℝ :=
  if i ∈ S then singleBlockDiagonalMean S g - Real.log (g.val i i) else 0

lemma singleBlockDiagonalWeights_sum {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (g : G n) :
    ∑ i, singleBlockDiagonalWeights S g i = 0 := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hsum : ∑ i, singleBlockDiagonalWeights S g i =
      ∑ i ∈ S, (singleBlockDiagonalMean S g - Real.log (g.val i i)) := by
    simp only [singleBlockDiagonalWeights, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  dsimp only [singleBlockDiagonalMean]
  field_simp [hcard]
  ring

@[irreducible] def singleBlockDiagonalCorrection {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) : G n :=
  diagonalOneParameter (singleBlockDiagonalWeights S g)
    (singleBlockDiagonalWeights_sum S hS g) 1

lemma singleBlockDiagonalCorrection_mem {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) :
    singleBlockDiagonalCorrection S hS g ∈ singleBlockRootGroup (↑S) := by
  unfold singleBlockDiagonalCorrection
  obtain ⟨i₀, hi₀⟩ := hS
  apply supported_diagonalOneParameter_mem_singleBlockRootGroup (↑S) i₀ hi₀
  intro i hi
  exact ite_eq_right hi

lemma mul_singleBlockDiagonalCorrection_mem {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (b u : G n)
    (hb : b ∈ blockRootGroup (singleBlockSetoid (↑S))) :
    b * singleBlockDiagonalCorrection S hS u ∈ singleBlockRootGroup (↑S) := by
  have hbk : b ∈ singleBlockRootGroup (↑S) := by
    rw [← blockRootGroup_singleBlockSetoid]
    exact hb
  exact (singleBlockRootGroup (↑S)).mul_mem
    (x := b) (y := singleBlockDiagonalCorrection S hS u)
    hbk (singleBlockDiagonalCorrection_mem S hS u)

lemma singleBlockDiagonalCorrection_entry {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) (i j : Fin n) :
    (g * singleBlockDiagonalCorrection S hS g).val i j =
      g.val i j * Real.exp (singleBlockDiagonalWeights S g j) := by
  unfold singleBlockDiagonalCorrection
  change (g.val * Matrix.diagonal (fun k =>
    Real.exp (singleBlockDiagonalWeights S g k * 1))) i j = _
  simp only [Matrix.mul_diagonal, mul_one]

lemma singleBlockDiagonalCorrection_diagonal {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (g : G n) (hpos : ∀ i ∈ S, 0 < g.val i i)
    (i : Fin n) (hi : i ∈ S) :
    (g * singleBlockDiagonalCorrection S hS g).val i i =
      Real.exp (singleBlockDiagonalMean S g) := by
  rw [singleBlockDiagonalCorrection_entry, singleBlockDiagonalWeights, ite_eq_left hi,
    Real.exp_sub, Real.exp_log (hpos i hi)]
  field_simp [ne_of_gt (hpos i hi)]

lemma singleBlockDiagonalCorrection_tendsto {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty) (g : ℕ → G n)
    (hg : Tendsto g atTop (𝓝 1)) :
    Tendsto (fun k => singleBlockDiagonalCorrection S hS (g k)) atTop (𝓝 1) := by
  have hi (i : Fin n) : Tendsto (fun k => Real.log ((g k).val i i)) atTop (𝓝 0) := by
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have he : Tendsto (fun k => (g k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] using hc.continuousAt.tendsto.comp hg
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp he
  have hmean : Tendsto (fun k => singleBlockDiagonalMean S (g k)) atTop (𝓝 0) := by
    simpa only [singleBlockDiagonalMean, Finset.sum_const_zero, zero_div] using
      (tendsto_finsetSum S (fun i _ => hi i)).div_const (S.card : ℝ)
  have hw (i : Fin n) : Tendsto (fun k => singleBlockDiagonalWeights S (g k) i)
      atTop (𝓝 0) := by
    by_cases hiS : i ∈ S
    · simpa only [singleBlockDiagonalWeights, ite_eq_left hiS, sub_zero] using hmean.sub (hi i)
    · simpa only [singleBlockDiagonalWeights, ite_eq_right hiS] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simp only [singleBlockDiagonalCorrection, diagonalOneParameter,
      Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, mul_one]
    simpa only [Function.comp_def, mul_one, Real.exp_zero] using
      (Real.continuous_exp.tendsto 0).comp (hw i)
  · unfold singleBlockDiagonalCorrection
    change Tendsto (fun k => (Matrix.diagonal (fun a =>
        Real.exp (singleBlockDiagonalWeights S (g k) a * 1))) i j)
      atTop (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j))
    simpa only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Both corrections remain in the single-block group. This is the
normalization available on its actual ergodic components. -/
theorem exists_singleBlock_transverse_sequence {n : ℕ}
    (S : Finset (Fin n)) (hS : S.Nonempty)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1)) :
    ∃ s b : ℕ → G n, ∃ c : ℕ → ℝ,
      Tendsto s atTop (𝓝 1) ∧ Tendsto b atTop (𝓝 1) ∧
      (∀ k, s k = g k * b k) ∧ (∀ k, b k ∈ singleBlockRootGroup (↑S)) ∧
      (∀ k, 0 < c k) ∧
      ∀ᶠ k in atTop, (∀ i ∈ S, (s k).val i i = c k) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (s k).val i j = 0 := by
  obtain ⟨u, b, hu, hb, he, hmem, hz⟩ :=
    exists_block_transverse_sequence (singleBlockSetoid (↑S)) g hg
  let a : ℕ → G n := fun k => singleBlockDiagonalCorrection S hS (u k)
  let s : ℕ → G n := fun k => u k * a k
  let b' : ℕ → G n := fun k => b k * a k
  let c : ℕ → ℝ := fun k => Real.exp (singleBlockDiagonalMean S (u k))
  have ha : Tendsto a atTop (𝓝 1) := singleBlockDiagonalCorrection_tendsto S hS u hu
  have hpos : ∀ᶠ k in atTop, ∀ i, 0 < (u k).val i i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun a : G n => a.val i i) := by fun_prop
    have hlim : Tendsto (fun k => (u k).val i i) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_def, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] using hc.continuousAt.tendsto.comp hu
    exact hlim.eventually (lt_mem_nhds zero_lt_one)
  refine ⟨s, b', c, ?_, ?_, ?_, ?_, fun k => Real.exp_pos _, ?_⟩
  · simpa only [s, mul_one] using hu.mul ha
  · simpa only [b', mul_one] using hb.mul ha
  · intro k
    dsimp only [s, b']
    rw [he k, mul_assoc]
  · intro k
    change b k * singleBlockDiagonalCorrection S hS (u k) ∈ singleBlockRootGroup (↑S)
    exact mul_singleBlockDiagonalCorrection_mem S hS (b k) (u k) (hmem k)
  · filter_upwards [hpos, hz] with k hk hkz
    constructor
    · intro i hi
      exact singleBlockDiagonalCorrection_diagonal S hS (u k) (fun j _ => hk j) i hi
    · intro i hi j hj hij
      change (u k * singleBlockDiagonalCorrection S hS (u k)).val i j = 0
      rw [singleBlockDiagonalCorrection_entry, hkz i j hij (Or.inr ⟨hi, hj⟩), zero_mul]

end DukePrimeDegree

end

end OAI
