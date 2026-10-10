import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingScale

namespace OAI

/-!
# Divergence of the normalized shearing time

For matrices approaching the identity, every time at which root
conjugation has a fixed nonzero displacement tends to infinity. This
places the stopping-time normalization on the scale required for the
recurrence and leafwise comparison argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma rootShearSize_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    rootShearSize hij 1 t = 0 := by
  simp only [rootShearSize, mul_one, Matrix.SpecialLinearGroup.transvection_mul_neg,
    sub_self, abs_zero, Finset.sum_const_zero]

lemma continuous_rootShearSize_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Continuous (fun z : G n × ℝ => rootShearSize hij z.1 z.2) := by
  have hroot := continuous_rootTransvection hij
  have hconj : Continuous (fun z : G n × ℝ =>
      Matrix.SpecialLinearGroup.transvection hij z.2 * z.1 *
        Matrix.SpecialLinearGroup.transvection hij (-z.2)) :=
    ((hroot.comp continuous_snd).mul continuous_fst).mul
      (hroot.comp continuous_snd.neg)
  unfold rootShearSize
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  exact ((((continuous_apply s).comp (continuous_apply r)).comp
    (continuous_subtype_val.comp hconj)).sub
      (((continuous_apply s).comp (continuous_apply r)).comp
        (continuous_subtype_val.comp continuous_fst))).abs

theorem rootShearScale_tendsto_atTop {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, 0 ≤ t m) {a : ℝ} (ha : a ≠ 0)
    (hsize : ∀ m, rootShearSize hij (g m) (t m) = a) :
    Tendsto t atTop atTop := by
  by_contra h
  rw [tendsto_atTop] at h
  push Not at h
  obtain ⟨R, hR⟩ := h
  have hbounded : ∃ᶠ m : ℕ in atTop, t m ∈ Icc 0 R :=
    hR.mono fun m hm => ⟨ht m, hm.le⟩
  obtain ⟨v, _, φ, hφ, hv⟩ := isCompact_Icc.isSeqCompact.subseq_of_frequently_in hbounded
  have hgp : Tendsto (g ∘ φ) atTop (𝓝 1) := hg.comp hφ.tendsto_atTop
  have hlim := (continuous_rootShearSize_pair hij).continuousAt.tendsto.comp
    (hgp.prodMk_nhds hv)
  have hlim0 : Tendsto (fun m => rootShearSize hij (g (φ m)) (t (φ m)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, rootShearSize_one] using hlim
  have hconst : Tendsto (fun m => rootShearSize hij (g (φ m)) (t (φ m)))
      atTop (𝓝 a) := by
    simpa only [hsize] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  exact ha (tendsto_nhds_unique hconst hlim0)

/-- Noncentral return matrices approaching the identity admit first
shearing intervals whose lengths diverge. -/
theorem exists_diverging_first_rootShearScale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hnot : ∀ m, ¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g m)
    {a : ℝ} (ha : 0 < a) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧ ∀ m,
      0 < t m ∧ rootShearSize hij (g m) (t m) = a ∧
        ∀ u ∈ Icc 0 (t m), rootShearSize hij (g m) u ≤ a := by
  choose t ht heq hsmall using fun m => exists_first_rootShearScale hij (g m) (hnot m) ha
  exact ⟨t, rootShearScale_tendsto_atTop hij g hg t (fun m => (ht m).le) ha.ne' heq,
    fun m => ⟨ht m, heq m, hsmall m⟩⟩

end DukePrimeDegree

end OAI
