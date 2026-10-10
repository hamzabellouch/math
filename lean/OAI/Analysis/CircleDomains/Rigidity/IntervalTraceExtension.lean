import OAI.Analysis.CircleDomains.Modulus.FiniteGapPayment

namespace OAI

/-!
# Endpoint traces from finite variation on an open interval

A differentiable function on an open bounded interval whose derivative
is integrable has an absolutely continuous extension to the closed
interval. This supplies the endpoint traces at the round holes in the
parallel-line argument, without assuming boundary continuity.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem exists_absolutelyContinuous_extension_of_integrable_derivative
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hi : IntervalIntegrable d volume a b) :
    ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ EqOn g f (Ioo a b) ∧
      Tendsto f (𝓝[Ioo a b] a) (𝓝 (g a)) ∧
      Tendsto f (𝓝[Ioo a b] b) (𝓝 (g b)) := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hcu : c ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hc
  let g : ℝ → ℝ := fun x => f c + ∫ t in c..x, d t
  have hg : AbsolutelyContinuousOnInterval g a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f c) a b :=
      (LipschitzWith.const (f c)).lipschitzOnWith.absolutelyContinuousOnInterval
    exact hconst.add (hi.absolutelyContinuousOnInterval_intervalIntegral hcu)
  have heq : EqOn g f (Ioo a b) := by
    intro x hx
    have hcx : uIcc c x ⊆ Ioo a b := by
      intro y hy
      rcases le_total c x with h | h
      · rw [uIcc_of_le h] at hy
        exact ⟨hc.1.trans_le hy.1, hy.2.trans_lt hx.2⟩
      · rw [uIcc_of_ge h] at hy
        exact ⟨hx.1.trans_le hy.1, hy.2.trans_lt hc.2⟩
    have hint : IntervalIntegrable d volume c x :=
      hi.mono_set (uIcc_subset_uIcc hcu (by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hx))
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hd y (hcx hy)) hint
    dsimp only [g]
    rw [hFTC]
    ring
  have hgc : ContinuousOn g (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hg.continuousOn
  refine ⟨g, hg, heq, ?_, ?_⟩
  · apply ((hgc a ⟨le_rfl, hab.le⟩).mono
      Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq hx
  · apply ((hgc b ⟨hab.le, le_rfl⟩).mono
      Ioo_subset_Icc_self).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact heq hx

theorem exists_absolutelyContinuous_extension_of_memLp_derivative
    {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (d x) x)
    (hd2 : MemLp d 2 (volume.restrict (Ioo a b))) :
    ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g a b ∧ EqOn g f (Ioo a b) ∧
      Tendsto f (𝓝[Ioo a b] a) (𝓝 (g a)) ∧
      Tendsto f (𝓝[Ioo a b] b) (𝓝 (g b)) := by
  let : IsFiniteMeasure (volume.restrict (Ioo a b)) :=
    isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  have hi : IntegrableOn d (Ioo a b) := hd2.integrable (by norm_num)
  exact exists_absolutelyContinuous_extension_of_integrable_derivative hab hd
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hi)

end CircleDomainRigidity

end OAI
