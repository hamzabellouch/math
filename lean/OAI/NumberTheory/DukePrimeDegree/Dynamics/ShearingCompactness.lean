import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingCentralizer

namespace OAI

/-!
# A nontrivial limit of normalized shearing

The normalized first shearing intervals provide bounded terminal
matrices. Finite-dimensional compactness supplies a convergent
subsequence, whose limit is nontrivial and centralizes the root group.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

def slMatrixDifference {n : ℕ} (g h : G n) : ℝ :=
  ∑ r, ∑ s, |g.1 r s - h.1 r s|

lemma continuous_slMatrixDifference {n : ℕ} :
    Continuous (fun z : G n × G n => slMatrixDifference z.1 z.2) := by
  unfold slMatrixDifference
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  have hentry : Continuous (fun g : G n => g.1 r s) := by fun_prop
  exact ((hentry.comp continuous_fst).sub (hentry.comp continuous_snd)).abs

lemma slMatrixDifference_self {n : ℕ} (g : G n) : slMatrixDifference g g = 0 := by
  simp [slMatrixDifference]

/-- A normalized, bounded shearing sequence has a nonidentity
subsequential limit in the root centralizer. -/
theorem exists_nontrivial_rootShearLimit {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 < t m) (htop : Tendsto t atTop atTop)
    {a : ℝ} (ha : 0 < a)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a)
    (hsmall : ∀ m, ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a) :
    ∃ h : G n, h ≠ 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
        Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) atTop (𝓝 h) ∧
      ∀ u : ℝ, h * Matrix.SpecialLinearGroup.transvection hij u =
        Matrix.SpecialLinearGroup.transvection hij u * h := by
  let H : ℕ → G n := fun m => Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
    Matrix.SpecialLinearGroup.transvection hij (-t m)
  have hcont (r s : Fin n) : Continuous (fun g : G n => g.1 r s) := by fun_prop
  have hgentry (r s : Fin n) : Tendsto (fun m => (g m).1 r s) atTop
      (𝓝 ((1 : G n).1 r s)) :=
    (hcont r s).tendsto _ |>.comp hg
  have hgsmall : ∀ᶠ m : ℕ in atTop, ∀ r s : Fin n, |(g m).1 r s| ≤ 2 := by
    apply Filter.eventually_all.mpr
    intro r
    apply Filter.eventually_all.mpr
    intro s
    have hval : |(1 : G n).1 r s| < (2 : ℝ) := by
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
      split_ifs <;> norm_num
    exact ((hgentry r s).abs.eventually (gt_mem_nhds hval)).mono fun _ hm => hm.le
  let K : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {M | ∀ r s, |M r s| ≤ a + 2}
  have hK : IsCompact K := by
    have hbox : IsCompact {M : Matrix (Fin n) (Fin n) ℝ |
        ∀ r s, M r s ∈ Icc (-(a + 2)) (a + 2)} :=
      isCompact_pi_infinite fun _ : Fin n =>
      isCompact_pi_infinite fun _ : Fin n =>
        (isCompact_Icc : IsCompact (Icc (-(a + 2)) (a + 2)))
    simpa only [K, mem_Icc, abs_le] using hbox
  have hHK : ∀ᶠ m : ℕ in atTop, (H m).1 ∈ K := by
    filter_upwards [hgsmall] with m hm
    intro r s
    calc
      |(H m).1 r s| = |((H m).1 r s - (g m).1 r s) + (g m).1 r s| :=
        by rw [sub_add_cancel]
      _ ≤ |(H m).1 r s - (g m).1 r s| + |(g m).1 r s| := abs_add_le _ _
      _ ≤ a + 2 := add_le_add
        ((entry_sub_le_rootShearSize hij (g m) (t m) r s).trans_eq (hsize m)) (hm r s)
  obtain ⟨M, _, φ, hφ, hM⟩ := hK.tendsto_subseq' hHK.frequently
  have hdet : M.det = 1 := by
    apply (isClosed_eq continuous_id.matrix_det continuous_const).mem_of_tendsto hM
    exact Filter.Eventually.of_forall fun m => (H (φ m)).property
  let h : G n := ⟨M, hdet⟩
  have hH : Tendsto (H ∘ φ) atTop (𝓝 h) := by
    apply tendsto_subtype_rng.mpr
    exact hM
  have hgp : Tendsto (g ∘ φ) atTop (𝓝 1) := hg.comp hφ.tendsto_atTop
  have hD := continuous_slMatrixDifference.continuousAt.tendsto.comp (hH.prodMk_nhds hgp)
  have hD' : Tendsto (fun m => slMatrixDifference (H (φ m)) (g (φ m)))
      atTop (𝓝 (slMatrixDifference h 1)) := by
    simpa only [Function.comp_def] using hD
  have hDc : Tendsto (fun m => slMatrixDifference (H (φ m)) (g (φ m)))
      atTop (𝓝 a) := by
    have he (m : ℕ) : slMatrixDifference (H (φ m)) (g (φ m)) = a := hsize (φ m)
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  have hne : h ≠ 1 := by
    intro he
    have hdiff := tendsto_nhds_unique hD' hDc
    rw [he, slMatrixDifference_self] at hdiff
    exact ha.ne' hdiff.symm
  refine ⟨h, hne, φ, hφ, hH, ?_⟩
  exact rootShearLimit_centralizes hij (g ∘ φ) hgp (t ∘ φ) (fun m => ht (φ m))
    (htop.comp hφ.tendsto_atTop) a (fun m => hsmall (φ m)) h hH

end DukePrimeDegree

end OAI
