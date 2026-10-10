import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSignedCentralizer

namespace OAI

/-!
# Bounded shearing intervals with signed return times

Selected annular returns may have either sign. A positive lower
terminal displacement and a bound on the symmetric interval produce a
nontrivial horospherical limit.
-/

noncomputable section
open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_signed_bounded_horospherical_rootShearLimit
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a B : ℝ) (ha : 0 < a)
    (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧
      a ≤ slMatrixDifference h 1 ∧ slMatrixDifference h 1 ≤ B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun m => Matrix.SpecialLinearGroup.transvection hij (t (φ m)) * g (φ m) *
          Matrix.SpecialLinearGroup.transvection hij (-t (φ m))) atTop (𝓝 h) := by
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
    {M | ∀ r s, |M r s| ≤ B + 2}
  have hK : IsCompact K := by
    have hbox : IsCompact {M : Matrix (Fin n) (Fin n) ℝ |
        ∀ r s, M r s ∈ Icc (-(B + 2)) (B + 2)} :=
      isCompact_pi_infinite fun _ : Fin n =>
      isCompact_pi_infinite fun _ : Fin n =>
        (isCompact_Icc : IsCompact (Icc (-(B + 2)) (B + 2)))
    simpa only [K, mem_Icc, abs_le] using hbox
  have hHK : ∀ᶠ m : ℕ in atTop, (H m).1 ∈ K := by
    filter_upwards [hgsmall] with m hm
    intro r s
    calc
      |(H m).1 r s| = |((H m).1 r s - (g m).1 r s) + (g m).1 r s| :=
        by rw [sub_add_cancel]
      _ ≤ |(H m).1 r s - (g m).1 r s| + |(g m).1 r s| := abs_add_le _ _
      _ ≤ B + 2 := add_le_add
        ((entry_sub_le_rootShearSize hij (g m) (t m) r s).trans
          (hsmall m (t m) le_rfl)) (hm r s)
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
  have hlow : a ≤ slMatrixDifference h 1 :=
    ge_of_tendsto hD' (Eventually.of_forall fun m => hsize (φ m))
  have hupp : slMatrixDifference h 1 ≤ B :=
    le_of_tendsto hD' (Eventually.of_forall fun m =>
      hsmall (φ m) (t (φ m)) le_rfl)
  have hcentral := rootShearLimit_signed_centralizes hij (g ∘ φ) hgp (t ∘ φ)
    (fun m => ht (φ m)) (htop.comp hφ.tendsto_atTop) B
    (fun m => hsmall (φ m)) h hH
  have hshape := rootShearLimit_horospherical hij (g ∘ φ) hgp (t ∘ φ) h hH (hcentral 1)
  have hne : h ≠ 1 := by
    intro he
    rw [he, slMatrixDifference_self] at hlow
    exact ha.not_ge hlow
  exact ⟨h, hne, hshape, hlow, hupp, φ, hφ, hH⟩

end DukePrimeDegree

end

end OAI
