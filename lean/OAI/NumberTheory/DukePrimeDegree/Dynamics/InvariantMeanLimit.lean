import OAI.NumberTheory.DukePrimeDegree.Dynamics.InvariantMeanGenericSet

namespace OAI

/-!
# The actual nonergodic invariant mean

The L2 mean ergodic theorem constructs the invariant observable used
by the uniform generic-set theorem.  Its integral agrees with the
original observable; it is not asserted to be constant.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

theorem exists_measurable_invariant_L1_mean
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (f : Y → ℝ) (hf : MemLp f 2 μ) :
    ∃ q : Y → ℝ, Measurable q ∧ Integrable q μ ∧
      (fun x => q (T x)) =ᵐ[μ] q ∧
      (∫ x, q x ∂μ) = ∫ x, f x ∂μ ∧
      Tendsto (fun N => ∫ x, |birkhoffAverage ℝ T f N x - q x| ∂μ)
        atTop (𝓝 0) := by
  let F : Lp ℝ 2 μ := hf.toLp f
  let V : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ T hT).toContinuousLinearMap
  have hVe : (V : Lp ℝ 2 μ → Lp ℝ 2 μ) = Lp.compMeasurePreserving T hT := by
    funext v
    rfl
  let A (N : ℕ) : Lp ℝ 2 μ := birkhoffAverage ℝ V id N F
  have hV : ‖V‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change ‖Lp.compMeasurePreserving T hT v‖ ≤ 1 * ‖v‖
    simpa only [one_mul] using (Lp.norm_compMeasurePreserving v hT).le
  let S := V.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let Q : Lp ℝ 2 μ := S.orthogonalProjectionOnto F
  have hAQ : Tendsto A atTop (𝓝 Q) := V.tendsto_birkhoffAverage_orthogonalProjection hV F
  have hfixed : Lp.compMeasurePreserving T hT Q = Q := by
    have hmem := (S.orthogonalProjectionOnto F).property
    change V Q = Q at hmem
    simpa only [hVe] using hmem
  let q : Y → ℝ := (Lp.aestronglyMeasurable Q).mk Q
  have hq : (Q : Y → ℝ) =ᵐ[μ] q := (Lp.aestronglyMeasurable Q).ae_eq_mk
  have hqm : Measurable q := (Lp.aestronglyMeasurable Q).measurable_mk
  have hqi : Integrable q μ :=
    (memLp_one_iff_integrable.mp ((Lp.memLp Q).mono_exponent (by norm_num))).congr hq
  have hqinvariant : (fun x => q (T x)) =ᵐ[μ] q := by
    filter_upwards [hT.quasiMeasurePreserving.ae_eq_comp hq, hq,
      Lp.coeFn_compMeasurePreserving Q hT] with x hshift hplain hcomp
    simp only [Function.comp_def] at hshift hcomp
    rw [← hshift, ← hcomp, hfixed, hplain]
  have hrep (N : ℕ) : (A N : Y → ℝ) =ᵐ[μ] birkhoffAverage ℝ T f N :=
    (Lp_orbit_average_ae μ T hT F N).trans
      (orbit_average_congr_ae μ T hT hf.coeFn_toLp N)
  have hmean : (∫ x, q x ∂μ) = ∫ x, f x ∂μ := by
    have hlim := (meanL2 μ).continuous.tendsto Q |>.comp hAQ
    have hconst : Tendsto (fun N => meanL2 μ (A N)) atTop (𝓝 (meanL2 μ F)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      exact (meanL2_birkhoffAverage μ T hT F N (Nat.ne_of_gt hN)).symm
    have heq := tendsto_nhds_unique hlim hconst
    rw [meanL2_apply, meanL2_apply] at heq
    exact (integral_congr_ae hq).symm.trans (heq.trans (integral_congr_ae hf.coeFn_toLp))
  refine ⟨q, hqm, hqi, hqinvariant, hmean, ?_⟩
  have hb (N : ℕ) :
      (∫ x, |birkhoffAverage ℝ T f N x - q x| ∂μ) ≤ ‖A N - Q‖ := by
    have heq : (∫ x, |birkhoffAverage ℝ T f N x - q x| ∂μ) =
        ∫ x, ‖(A N - Q) x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrep N, hq, Lp.coeFn_sub (A N) Q] with x hx hqx hs
      simp only [hs, Pi.sub_apply, hx, hqx, Real.norm_eq_abs]
    rw [heq]
    exact integral_norm_le_L2_norm μ _
  have hnorm : Tendsto (fun N => ‖A N - Q‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hAQ.sub_const Q).norm
  exact squeeze_zero (fun N => integral_nonneg (fun x => abs_nonneg _)) hb hnorm

/-- A bounded observable has fixed uniform generic sets around its
actual invariant mean, even for a nonergodic sampling transformation. -/
theorem exists_invariant_mean_with_uniform_generic_sets
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Y → Y) (hT : MeasurePreserving T μ μ)
    (f : Y → ℝ) (hfm : Measurable f)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C) :
    ∃ q : Y → ℝ, Measurable q ∧ Integrable q μ ∧
      (fun x => q (T x)) =ᵐ[μ] q ∧ (∫ x, q x ∂μ) = ∫ x, f x ∂μ ∧
      ∀ ε δ : ℝ, 0 < ε → 0 < δ →
        ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal δ ∧
          ∃ N₀ : ℕ, ∀ x ∈ G, ∀ N ≥ N₀,
            |birkhoffAverage ℝ T f N x - q x| ≤ ε := by
  have hf : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  obtain ⟨q, hqm, hqi, hqinv, hqmean, hlim⟩ := exists_measurable_invariant_L1_mean μ T hT f hf
  refine ⟨q, hqm, hqi, hqinv, hqmean, ?_⟩
  intro ε δ hε hδ
  exact exists_uniform_invariant_mean_set μ T hT f hfm
    (memLp_one_iff_integrable.mp (hf.mono_exponent (by norm_num)))
    C hC0 hC q hqm hqi hqinv hlim ε δ hε hδ

end DukePrimeDegree

end

end OAI
