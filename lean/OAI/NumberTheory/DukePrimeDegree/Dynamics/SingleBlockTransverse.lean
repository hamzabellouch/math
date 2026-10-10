import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockNormalization
import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockMatrixProjection

namespace OAI

/-!
# A single-block correction retains a transverse limiting shear

Only the selected block is normalized to a scalar. Its complement may
have arbitrary entries. Conjugation by the selected root group fixes
the entire block-diagonal part, so every nonidentity limiting shear is
outside the two-block preserving group.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockComplementSetoid {n : ℕ} (S : Set (Fin n)) : Setoid (Fin n) where
  r i j := i ∈ S ↔ j ∈ S
  iseqv := ⟨fun _ => Iff.rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

lemma singleBlockRootGroup_le_blockComplement {n : ℕ} (S : Set (Fin n)) :
    singleBlockRootGroup S ≤ blockMatrixGroup (blockComplementSetoid S) := by
  apply singleBlockRootGroup_le_of_roots
  intro i hi j hj hij t
  exact blockRootGroup_le_blockMatrixGroup (blockComplementSetoid S)
    (root_mem_blockRootGroup (blockComplementSetoid S) i j hij
      ⟨fun _ => hj, fun _ => hi⟩ t)

lemma matrix_commute_transvection_of_row_column {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (t : ℝ)
    (hcol : ∀ a, a ≠ i → M a i = 0)
    (hrow : ∀ b, b ≠ j → M j b = 0)
    (hdiag : M i i = M j j) :
    Commute M (Matrix.transvection i j t) := by
  change M * Matrix.transvection i j t = Matrix.transvection i j t * M
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst a
    subst b
    simp only [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      hdiag]
  · subst a
    rw [Matrix.mul_transvection_apply_of_ne i j i b hb t M,
      Matrix.transvection_mul_apply_same, hrow b hb, mul_zero, add_zero]
  · subst b
    rw [Matrix.mul_transvection_apply_same,
      Matrix.transvection_mul_apply_of_ne i j a j ha t M,
      hcol a ha, mul_zero, add_zero]
  · rw [Matrix.mul_transvection_apply_of_ne i j a b hb t M,
      Matrix.transvection_mul_apply_of_ne i j a b ha t M]

lemma withinBlockPart_singleBlock_commutes {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ singleBlockRootGroup S) :
    slMatrixConjugation u (withinBlockPart (blockComplementSetoid S) g.val) =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let M := withinBlockPart (blockComplementSetoid S) g.val
  have hroot (i : Fin n) (hi : i ∈ S) (j : Fin n) (hj : j ∈ S)
      (hij : i ≠ j) (t : ℝ) :
      slMatrixConjugation (Matrix.SpecialLinearGroup.transvection hij t) M = M := by
    apply slMatrixConjugation_eq_self
    apply matrix_commute_transvection_of_row_column
    · intro a hai
      by_cases haS : a ∈ S
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show (a ∈ S ↔ i ∈ S) from ⟨fun _ => hi, fun _ => haS⟩,
          ite_true, hzero a haS i hi hai]
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show ¬ (a ∈ S ↔ i ∈ S) from fun h => haS (h.mpr hi), ite_false]
    · intro b hbj
      by_cases hbS : b ∈ S
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show (j ∈ S ↔ b ∈ S) from ⟨fun _ => hbS, fun _ => hj⟩,
          ite_true, hzero j hj b hbS hbj.symm]
      · simp only [M, withinBlockPart, blockComplementSetoid,
          show ¬ (j ∈ S ↔ b ∈ S) from fun h => hbS (h.mp hj), ite_false]
    · simp only [M, withinBlockPart, Setoid.refl, ite_true, hdiag i hi, hdiag j hj]
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      obtain ⟨i, j, hij, t, hi, hj, rfl⟩ := hu
      exact hroot i hi j hj hij t
  | one => exact slMatrixConjugation_one M
  | mul u v _ _ hu hv => rw [slMatrixConjugation_mul, hu, hv]
  | inv u _ hu =>
      have he := congrArg (slMatrixConjugation u⁻¹) hu
      have hinv := slMatrixConjugation_inverse u⁻¹ M
      rw [inv_inv] at hinv
      exact he.symm.trans hinv

theorem withinBlockPart_singleBlock_conjugation {n : ℕ}
    (S : Set (Fin n)) (g : G n) (c : ℝ)
    (hdiag : ∀ i ∈ S, g.val i i = c)
    (hzero : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → g.val i j = 0)
    (u : G n) (hu : u ∈ singleBlockRootGroup S) :
    withinBlockPart (blockComplementSetoid S) (u * g * u⁻¹).val =
      withinBlockPart (blockComplementSetoid S) g.val := by
  let r := blockComplementSetoid S
  have hb : u ∈ blockMatrixGroup r := singleBlockRootGroup_le_blockComplement S hu
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
    withinBlockPart_mul_left r u.val _ (cross_zero_of_mem_blockMatrixGroup r u hb),
    withinBlockPart_mul_right r g.val u⁻¹.val
      (cross_zero_of_mem_blockMatrixGroup r u⁻¹ ((blockMatrixGroup r).inv_mem hb))]
  simpa only [slMatrixConjugation, inv_inv, Matrix.mul_assoc] using
    withinBlockPart_singleBlock_commutes S g c hdiag hzero u⁻¹
      ((singleBlockRootGroup S).inv_mem hu)

theorem singleBlock_conjugation_limit_outside_blocks {n : ℕ}
    (S : Set (Fin n)) (g u : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hu : ∀ k, u k ∈ singleBlockRootGroup S)
    (hpart : ∀ᶠ k in atTop,
      (∀ i ∈ S, (g k).val i i = c k) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g k).val i j = 0)
    (h : G n) (hne : h ≠ 1)
    (hlim : Tendsto (fun k => u k * g k * (u k)⁻¹) atTop (𝓝 h)) :
    h ∉ blockMatrixGroup (blockComplementSetoid S) := by
  intro hh
  apply hne
  apply Subtype.ext
  ext i j
  by_cases hij : blockComplementSetoid S i j
  · have he : ∀ᶠ k in atTop,
        (u k * g k * (u k)⁻¹).val i j = (g k).val i j := by
      filter_upwards [hpart] with k hk
      have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
        (withinBlockPart_singleBlock_conjugation S (g k) (c k) hk.1 hk.2 (u k) (hu k))
      simpa only [withinBlockPart, hij, ite_true] using he
    have hc : Continuous (fun a : G n => a.val i j) := by fun_prop
    have hx := hc.continuousAt.tendsto.comp hg
    have hy := hc.continuousAt.tendsto.comp hlim
    exact tendsto_nhds_unique hy (hx.congr' (he.mono fun _ h => h.symm))
  · rw [cross_zero_of_mem_blockMatrixGroup (blockComplementSetoid S) h hh i j hij]
    have hneij : i ≠ j := by
      intro he
      subst j
      exact hij Iff.rfl
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hneij]

end DukePrimeDegree

end

end OAI
