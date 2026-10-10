import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace SharpTerminalLeave

section Forcing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem variation_of_constants (A : E →L[ℝ] E) (z f : ℝ → E)
    {s : ℝ} (hs : 0 ≤ s) (hz : ContinuousOn z (Set.Icc 0 s))
    (hf : ContinuousOn f (Set.Icc 0 s))
    (hd : ∀ t ∈ Set.Ioo 0 s, HasDerivAt z (-A (z t) + f t) t) :
    z s = NormedSpace.exp ((-s) • A) (z 0) +
      ∫ t in (0 : ℝ)..s, NormedSpace.exp ((t - s) • A) (f t) := by
  let w : ℝ → E := fun t => NormedSpace.exp ((t - s) • A) (z t)
  let g : ℝ → E := fun t => NormedSpace.exp ((t - s) • A) (f t)
  have he : Continuous (fun t : ℝ => NormedSpace.exp ((t - s) • A)) :=
    (differentiable_exp_smul_const ℝ A).continuous.comp
      (continuous_id.sub continuous_const)
  have hw : ContinuousOn w (Set.Icc 0 s) := he.continuousOn.clm_apply hz
  have hg : ContinuousOn g (Set.Icc 0 s) := he.continuousOn.clm_apply hf
  have hw' : ∀ t ∈ Set.Ioo 0 s, HasDerivAt w (g t) t := by
    intro t ht
    have he' := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t - s)).scomp t
      ((hasDerivAt_id t).sub_const s)
    have hh := he'.clm_apply (hd t ht)
    simp only [Function.comp_apply, id_eq, one_smul] at hh
    convert hh using 1
    simp [g, map_add, map_neg]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hw hw'
    (hg.intervalIntegrable_of_Icc hs)
  simp only [w, sub_self, zero_smul, NormedSpace.exp_zero,
    one_apply_eq_self, zero_sub] at hi
  change z s = _ + ∫ t in (0 : ℝ)..s, g t
  rw [hi]
  abel

theorem forcing_norm_bound (A : E →L[ℝ] E) (z f : ℝ → E)
    {s K d : ℝ} (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hz : ContinuousOn z (Set.Icc 0 s)) (hf : ContinuousOn f (Set.Icc 0 s))
    (hz0 : z 0 = 0)
    (hd : ∀ t ∈ Set.Ioo 0 s, HasDerivAt z (-A (z t) + f t) t)
    (hsem : ∀ u ∈ Set.Icc 0 s, ‖NormedSpace.exp ((-u) • A)‖ ≤ K)
    (hforce : ∀ t ∈ Set.Icc 0 s, ‖f t‖ ≤ d) : ‖z s‖ ≤ K * d * s := by
  rw [variation_of_constants A z f hs hz hf hd, hz0, map_zero, zero_add]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := K * d)
    (f := fun t => NormedSpace.exp ((t - s) • A) (f t)) (by
      intro t ht
      have ht0 : t ∈ Set.Ioc 0 s := by simpa only [Set.uIoc_of_le hs] using ht
      have ht' : t ∈ Set.Icc 0 s := ⟨ht0.1.le, ht0.2⟩
      have hu : s - t ∈ Set.Icc 0 s := ⟨sub_nonneg.mpr ht'.2, by linarith [ht'.1]⟩
      have he : ‖NormedSpace.exp ((t - s) • A)‖ ≤ K := by
        simpa only [neg_sub] using hsem (s - t) hu
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul he (hforce t ht') (norm_nonneg _) hK))
  simpa only [sub_zero, abs_of_nonneg hs] using hh

end Forcing

theorem strict_bootstrap {Q : ℝ → ℝ} {S δ : ℝ} (hδ : 0 < δ)
    (hQ : ContinuousOn Q (Set.Icc 0 S)) (hzero : Q 0 ≤ δ)
    (himprove : ∀ t ∈ Set.Icc 0 S,
      (∀ u ∈ Set.Icc 0 t, Q u ≤ δ) → Q t ≤ δ / 2) :
    ∀ t ∈ Set.Icc 0 S, Q t ≤ δ / 2 := by
  let B : Set ℝ := {t | Q t ≤ δ}
  have hclosed : IsClosed (B ∩ Set.Icc 0 S) := by
    simpa only [B, Set.preimage, Set.mem_Iic, Set.inter_comm] using
      hQ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hB : Set.Icc 0 S ⊆ B := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
    intro t ht hp
    have ht' : t ∈ Set.Icc 0 S := ⟨ht.1, ht.2.le⟩
    have him : Q t < δ := lt_of_le_of_lt (himprove t ht' hp) (by linarith)
    have hc := hQ t ht'
    have hI : Set.Icc 0 S ∈ 𝓝[>] t := by
      have hh : Set.Icc t S ∈ 𝓝[≥] t := Icc_mem_nhdsGE ht.2
      exact (nhdsWithin_mono t Set.Ioi_subset_Ici_self)
        (Filter.mem_of_superset hh (Set.Icc_subset_Icc_left ht.1))
    have hc' : ContinuousWithinAt Q (Set.Ioi t) t := hc.mono_of_mem_nhdsWithin hI
    have hsmall : ∀ᶠ u in 𝓝[>] t, Q u < δ := hc' (Iio_mem_nhds him)
    exact hsmall.mono (fun _ hu => hu.le)
  intro t ht
  apply himprove t ht
  intro u hu
  exact hB ⟨hu.1, hu.2.trans ht.2⟩

end SharpTerminalLeave

end
end

end OAI
