import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockShearingLimit
import OAI.NumberTheory.DukePrimeDegree.Dynamics.CompactStabilizerSeparation

namespace OAI

/-!
# A fixed compact set of transverse shearing limits

Normalizing the selected block makes the within-block part of every
limiting conjugate equal to the identity. A fixed positive displacement
therefore gives a compact set disjoint from the block group. Local
containment of the actual stabilizer in that group supplies a sufficiently
small displacement, before the generic points or the limiting shear are
chosen.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma entry_sub_le_slMatrixDifference {n : ℕ} (g h : G n) (i j : Fin n) :
    |g.val i j - h.val i j| ≤ slMatrixDifference g h := by
  apply (Finset.single_le_sum (f := fun k : Fin n => |g.val i k - h.val i k|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
  exact Finset.single_le_sum
    (f := fun k : Fin n => ∑ l : Fin n, |g.val k l - h.val k l|)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

lemma continuous_withinBlockPart {n : ℕ} (r : Setoid (Fin n)) :
    Continuous (withinBlockPart r) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : r i j
  · simpa only [withinBlockPart, hij, ite_true, Function.comp_def] using
      ((continuous_apply j).comp (continuous_apply i))
  · simpa only [withinBlockPart, hij, ite_false] using
      (continuous_const : Continuous (fun _ : Matrix (Fin n) (Fin n) ℝ => (0 : ℝ)))

def transverseMatrixShell {n : ℕ} (r : Setoid (Fin n)) (a : ℝ) : Set (G n) :=
  {g | withinBlockPart r g.val = 1 ∧ slMatrixDifference g 1 = a}

lemma transverseMatrixShell_isClosed {n : ℕ} (r : Setoid (Fin n)) (a : ℝ) :
    IsClosed (transverseMatrixShell r a) := by
  exact (isClosed_eq ((continuous_withinBlockPart r).comp continuous_subtype_val)
    continuous_const).inter
      (isClosed_eq (continuous_slMatrixDifference.comp
        (continuous_id.prodMk continuous_const)) continuous_const)

lemma transverseMatrixShell_isCompact {n : ℕ} (r : Setoid (Fin n)) (a : ℝ) :
    IsCompact (transverseMatrixShell r a) := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | ∀ i j, M i j ∈ Icc (-(|a| + 1)) (|a| + 1)}
  have hK : IsCompact K :=
    isCompact_pi_infinite fun _ : Fin n =>
      isCompact_pi_infinite fun _ : Fin n => isCompact_Icc
  apply (Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage hK).of_isClosed_subset
    (transverseMatrixShell_isClosed r a)
  intro g hg i j
  have hb : |g.val i j - (1 : G n).val i j| ≤ |a| :=
    ((entry_sub_le_slMatrixDifference g 1 i j).trans_eq hg.2).trans (le_abs_self a)
  have hone : |(1 : G n).val i j| ≤ (1 : ℝ) := by
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    split_ifs <;> norm_num
  apply abs_le.mp
  calc
    |g.val i j| = |(g.val i j - (1 : G n).val i j) + (1 : G n).val i j| := by
      rw [sub_add_cancel]
    _ ≤ |g.val i j - (1 : G n).val i j| + |(1 : G n).val i j| := abs_add_le _ _
    _ ≤ |a| + 1 := add_le_add hb hone

lemma transverseMatrixShell_not_mem_block {n : ℕ} (r : Setoid (Fin n))
    {a : ℝ} (ha : 0 < a) {g : G n} (hg : g ∈ transverseMatrixShell r a) :
    g ∉ blockMatrixGroup r := by
  intro hblock
  have heq : g = 1 := by
    apply Subtype.ext
    ext i j
    by_cases hij : r i j
    · have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hg.1
      simpa only [withinBlockPart, hij, ite_true, Matrix.SpecialLinearGroup.coe_one] using he
    · rw [cross_zero_of_mem_blockMatrixGroup r g hblock i j hij]
      have hne : i ≠ j := fun h => hij (h ▸ r.refl i)
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hne]
  have hz := hg.2
  rw [heq, slMatrixDifference_self] at hz
  exact ha.ne' hz.symm

section LocalShell

attribute [local irreducible] blockMatrixGroup

/-- Local block preservation gives a displacement scale whose entire
transverse shell is disjoint from the actual subgroup. -/
theorem exists_small_transverse_shell {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hlocal : {g : L | g.val ∈ blockMatrixGroup r} ∈ 𝓝 (1 : L)) :
    ∃ a : ℝ, 0 < a ∧ ∀ g ∈ transverseMatrixShell r a, g ∉ L := by
  obtain ⟨V, hV, hVL⟩ :=
    (mem_nhds_subtype (L : Set (G n)) (1 : L)
      {g : L | g.val ∈ blockMatrixGroup r}).mp hlocal
  obtain ⟨δ, hδ, hδV⟩ := matrixBall_nhds_basis hV
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro g hg hgL
  have hgδ : g ∈ matrixBall n δ := by
    intro i j
    have he := (entry_sub_le_slMatrixDifference g 1 i j).trans_eq hg.2
    exact he.trans_lt (by linarith)
  exact transverseMatrixShell_not_mem_block r (half_pos hδ) hg
    (hVL (show (⟨g, hgL⟩ : L) ∈ (Subtype.val : L → G n) ⁻¹' V from hδV hgδ))

end LocalShell

theorem singleBlock_conjugation_limit_withinPart {n : ℕ}
    (S : Set (Fin n)) (g u : ℕ → G n) (c : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 1))
    (hu : ∀ k, u k ∈ singleBlockRootGroup S)
    (hpart : ∀ᶠ k in atTop,
      (∀ i ∈ S, (g k).val i i = c k) ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (g k).val i j = 0)
    (h : G n)
    (hlim : Tendsto (fun k => u k * g k * (u k)⁻¹) atTop (𝓝 h)) :
    withinBlockPart (blockComplementSetoid S) h.val = 1 := by
  ext i j
  by_cases hij : blockComplementSetoid S i j
  · have he : ∀ᶠ k in atTop,
        (u k * g k * (u k)⁻¹).val i j = (g k).val i j := by
      filter_upwards [hpart] with k hk
      have ht := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
        (withinBlockPart_singleBlock_conjugation S (g k) (c k) hk.1 hk.2 (u k) (hu k))
      simpa only [withinBlockPart, hij, ite_true] using ht
    have hc : Continuous (fun a : G n => a.val i j) := by fun_prop
    have hentry := tendsto_nhds_unique (hc.continuousAt.tendsto.comp hlim)
      ((hc.continuousAt.tendsto.comp hg).congr' (he.mono fun _ h => h.symm))
    simpa only [withinBlockPart, hij, ite_true, Matrix.SpecialLinearGroup.coe_one] using hentry
  · have hne : i ≠ j := fun he => hij (he ▸ Iff.rfl)
    simp only [withinBlockPart, hij, ite_false, Matrix.one_apply_ne hne]

/-- The finitely many tests are fixed using the local stabilizer before
the normalized pairs and their subsequences are selected. -/
theorem exists_finite_small_transverse_separators {n : ℕ}
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (r : Setoid (Fin n))
    (hlocal : {g : invariantRightSubgroup μ | g.val ∈ blockMatrixGroup r} ∈
      𝓝 (1 : invariantRightSubgroup μ)) :
    ∃ a : ℝ, 0 < a ∧
      ∃ (F : Finset (CompactlySupportedContinuousMap (X n) ℝ)) (ε : ℝ),
        0 < ε ∧ ∀ g ∈ transverseMatrixShell r a,
          ∃ f ∈ F, ε < |invarianceDefect μ f g| := by
  obtain ⟨a, ha, hout⟩ := exists_small_transverse_shell (invariantRightSubgroup μ) r hlocal
  obtain ⟨F, ε, hε, hF⟩ := exists_finite_compact_stabilizer_separators μ
    (transverseMatrixShell r a) (transverseMatrixShell_isCompact r a) hout
  exact ⟨a, ha, F, ε, hε, hF⟩

end DukePrimeDegree

end

end OAI
