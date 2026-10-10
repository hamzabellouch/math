import OAI.Analysis.Brenier.DensityCDF
import OAI.Analysis.Brenier.Sections

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace Problem358
namespace AffineSlice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The scalar projection of a convex body's interior is a bounded open interval,
and its whole projection lies in the corresponding closed interval. -/
theorem exists_projection_interval {K : Set (ℝ × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∃ a b : ℝ, a < b ∧ Prod.fst '' interior K = Ioo a b ∧
      Prod.fst '' K ⊆ Icc a b := by
  let S : Set ℝ := Prod.fst '' interior K
  have hS : IsOpen S := isOpenMap_fst _ isOpen_interior
  have hSc : Convex ℝ S := hconv.interior.linear_image (LinearMap.fst ℝ ℝ V)
  have hSn : S.Nonempty := hne.image Prod.fst
  have hsub : S ⊆ Prod.fst '' K := Set.image_mono interior_subset
  have hbound := (hK.image continuous_fst).isBounded.subset hsub
  have hI := SectionMeasure.eq_Ioo_csInf_csSup_of_open_convex
    hS hSc hSn hbound.bddBelow hbound.bddAbove
  have hab : sInf S < sSup S := by
    obtain ⟨x, hx⟩ := hSn
    rw [hI] at hx
    exact hx.1.trans hx.2
  refine ⟨sInf S, sSup S, hab, hI, ?_⟩
  have hclosure : K = closure (interior K) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.isClosed.closure_eq]
  calc
    Prod.fst '' K = Prod.fst '' closure (interior K) := congrArg _ hclosure
    _ ⊆ closure S := image_closure_subset_closure_image continuous_fst
    _ = Icc (sInf S) (sSup S) := by
      nth_rw 1 [hI]
      exact closure_Ioo hab.ne

/-- Fubini identity for the real-valued volume of compact fibers. -/
theorem integral_fiberMeasureReal (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) :
    (∫ t, μ.real (fiber K t)) = (volume.prod μ).real K := by
  have hm : Measurable (fun t : ℝ => μ (fiber K t)) :=
    measurable_measure_prodMk_left hK.measurableSet
  have hlen : (∫⁻ t, μ (fiber K t)) = (volume.prod μ) K :=
    (Measure.prod_apply hK.measurableSet).symm
  change (∫ t, (μ (fiber K t)).toReal) = ((volume.prod μ) K).toReal
  rw [integral_toReal hm.aemeasurable (ae_of_all _ fun t => (isCompact_fiber hK t).measure_lt_top),
    hlen]

theorem integrable_fiberMeasureReal (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) :
    Integrable (fun t => μ.real (fiber K t)) volume := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_measure_prodMk_left hK.measurableSet).aemeasurable
  rw [← Measure.prod_apply hK.measurableSet]
  exact hK.measure_ne_top

/-- A compact convex body supplies an actual positive normalized 1D section density. -/
theorem exists_positiveIntervalDensity_of_convex_body
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) :
    ∃ D : PositiveIntervalDensity,
      D.density = (fun t => μ.real (fiber K t) / (volume.prod μ).real K) ∧
      Ioo D.lower D.upper = Prod.fst '' interior K := by
  obtain ⟨a, b, hab, hproj, hprojK⟩ := exists_projection_interval hK hconv hne
  let M : ℝ := (volume.prod μ).real K
  have hM : 0 < M := ENNReal.toReal_pos
    (measure_pos_of_nonempty_interior (volume.prod μ) hne).ne' hK.measure_ne_top
  have hm := integrable_fiberMeasureReal μ hK
  have hzero : ∀ t, t ∉ Icc a b → μ.real (fiber K t) = 0 := by
    intro t ht
    have hemp : fiber K t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact ht (hprojK ⟨(t, v), hv, rfl⟩)
    simp [hemp]
  have hint : (∫ t in a..b, μ.real (fiber K t)) = M := by
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact integral_fiberMeasureReal μ hK
  refine ⟨{
    lower := a
    upper := b
    density := fun t => μ.real (fiber K t) / M
    lower_lt_upper := hab
    integrable := (hm.div_const M).intervalIntegrable
    continuousOn := ?_
    positive := ?_
    integral_one := ?_ }, rfl, hproj.symm⟩
  · intro t ht
    have htp : ∃ v : V, (t, v) ∈ interior K := by
      have hmem : t ∈ Prod.fst '' interior K := hproj ▸ ht
      obtain ⟨⟨u, v⟩, huv, hu⟩ := hmem
      exact ⟨v, by simpa only using hu ▸ huv⟩
    exact ((continuousAt_fiberMeasureReal μ hK hconv htp).div_const M).continuousWithinAt
  · intro t ht
    have hmem : t ∈ Prod.fst '' interior K := hproj ▸ ht
    obtain ⟨⟨u, v⟩, huv, hu⟩ := hmem
    have htp : ∃ v : V, (t, v) ∈ interior K := ⟨v, by simpa only using hu ▸ huv⟩
    exact div_pos (fiberMeasureReal_pos μ hK htp) hM
  · rw [intervalIntegral.integral_div, hint, div_self hM.ne']

/-- The density object obtained from a convex body has exactly its scalar marginal law. -/
theorem densityMeasure_eq_scalar_marginal
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) (D : PositiveIntervalDensity)
    (hden : D.density = fun t => μ.real (fiber K t) / (volume.prod μ).real K)
    (hI : Ioo D.lower D.upper = Prod.fst '' interior K) :
    D.densityMeasure = Measure.map Prod.fst
      (((volume.prod μ) K)⁻¹ • (volume.prod μ).restrict K) := by
  have hM : 0 < (volume.prod μ).real K := ENNReal.toReal_pos
    (measure_pos_of_nonempty_interior (volume.prod μ) hne).ne' hK.measure_ne_top
  have hclosure : K = closure (interior K) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hK.isClosed.closure_eq]
  have hproj : Prod.fst '' K ⊆ Icc D.lower D.upper := calc
    Prod.fst '' K = Prod.fst '' closure (interior K) := congrArg _ hclosure
    _ ⊆ closure (Prod.fst '' interior K) := image_closure_subset_closure_image continuous_fst
    _ = closure (Ioo D.lower D.upper) := congrArg closure hI.symm
    _ = Icc D.lower D.upper := closure_Ioo D.lower_lt_upper.ne
  rw [SectionMarginal.map_fst_normalized_restrict volume μ K hK.measurableSet]
  change (volume.restrict (Ioo D.lower D.upper)).withDensity
    (fun t => ENNReal.ofReal (D.density t)) =
    ((volume.prod μ) K)⁻¹ • volume.withDensity (fun t => μ (fiber K t))
  have hm : Measurable (fun t : ℝ => μ (fiber K t)) :=
    measurable_measure_prodMk_left hK.measurableSet
  rw [← withDensity_indicator measurableSet_Ioo, ← withDensity_smul _ hm]
  apply withDensity_congr_ae
  filter_upwards [volume.ae_ne D.lower, volume.ae_ne D.upper] with t hl hu
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases ht : t ∈ Ioo D.lower D.upper
  · rw [indicator_of_mem ht, hden]
    change ENNReal.ofReal ((μ (fiber K t)).toReal / ((volume.prod μ) K).toReal) = _
    change 0 < ((volume.prod μ) K).toReal at hM
    rw [ENNReal.ofReal_div_of_pos hM,
      ENNReal.ofReal_toReal (isCompact_fiber hK t).measure_ne_top,
      ENNReal.ofReal_toReal hK.measure_ne_top, div_eq_mul_inv, mul_comm]
  · rw [indicator_of_notMem ht]
    have hemp : fiber K t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hp := hproj ⟨(t, v), hv, rfl⟩
      exact ht ⟨lt_of_le_of_ne hp.1 (Ne.symm hl), lt_of_le_of_ne hp.2 hu⟩
    simp [hemp]

/-- A scalar conditional quantile with its actual body marginal, not merely an abstract density law. -/
theorem exists_scalar_quantile_of_convex_body
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (ℝ × V)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) :
    ∃ Q : ℝ → ℝ, Continuous Q ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, Q s ∈ Prod.fst '' interior K) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Q
        ((volume.prod μ).real K / μ.real (fiber K (Q s))) s) ∧
      Measure.map Q (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst (((volume.prod μ) K)⁻¹ • (volume.prod μ).restrict K) := by
  obtain ⟨D, hden, hI⟩ := exists_positiveIntervalDensity_of_convex_body μ hK hconv hne
  refine ⟨D.quantileReal, D.quantileReal_continuous, ?_, ?_, ?_⟩
  · intro s hs
    rw [← hI]
    exact D.quantileReal_mem_interior hs
  · intro s hs
    have h := D.quantileReal_hasDerivAt hs
    rw [hden, inv_div] at h
    exact h
  · rw [D.map_quantileReal_uniform]
    exact densityMeasure_eq_scalar_marginal μ hK hconv hne D hden hI

end AffineSlice
end Problem358

end

noncomputable section
open MeasureTheory Set

namespace Problem358
namespace PositiveIntervalDensity

/-- The endpoints of any chosen interval-density description are measurable when
the intervals are precisely the fibers of an open set. No measurability of the
choice of density bundles is needed. -/
theorem measurable_endpoints_of_open_fibers {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (D : (Prod.fst '' U) → PositiveIntervalDensity)
    (hsupport : ∀ a, Ioo (D a).lower (D a).upper = SectionMeasure.fiber U a.val) :
    Measurable (fun a => (D a).lower) ∧ Measurable (fun a => (D a).upper) := by
  have hl : (fun a => (D a).lower) =
      (fun a : Prod.fst '' U => sInf (SectionMeasure.fiber U a.val)) := by
    funext a
    rw [← hsupport a, csInf_Ioo (D a).lower_lt_upper]
  have hr : (fun a => (D a).upper) =
      (fun a : Prod.fst '' U => sSup (SectionMeasure.fiber U a.val)) := by
    funext a
    rw [← hsupport a, csSup_Ioo (D a).lower_lt_upper]
  constructor
  · rw [hl]
    apply SectionMeasure.measurable_fiber_inf hU
    intro a ha
    rw [← hsupport ⟨a, ha⟩]
    exact bddBelow_Ioo
  · rw [hr]
    apply SectionMeasure.measurable_fiber_sup hU
    intro a ha
    rw [← hsupport ⟨a, ha⟩]
    exact bddAbove_Ioo

/-- Existential positive-density data on each open scalar fiber already determine
a jointly measurable family of actual quantile transports. In particular arbitrary
choices of the scalar density bundles do not leave a parameter-measurability gap. -/
theorem exists_quantiles_of_open_fiber_densities {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U) (p : A × ℝ → ℝ) (hp : Measurable p)
    (hex : ∀ a : Prod.fst '' U, ∃ D : PositiveIntervalDensity,
      D.density = (fun t => p (a.val, t)) ∧
      Ioo D.lower D.upper = SectionMeasure.fiber U a.val) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a : Prod.fst '' U, Measure.map (fun s => Q (a.val, s))
        (volume.restrict (Ioo (0 : ℝ) 1)) =
          (volume.restrict (SectionMeasure.fiber U a.val)).withDensity
            (fun t => ENNReal.ofReal (p (a.val, t)))) ∧
      (∀ a : Prod.fst '' U, ∀ s ∈ Ioo (0 : ℝ) 1, (a.val, Q (a.val, s)) ∈ U) ∧
      (∀ a : Prod.fst '' U, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (a.val, t)) (p (a.val, Q (a.val, s)))⁻¹ s) ∧
      (∀ a : Prod.fst '' U, StrictMonoOn (fun s => Q (a.val, s)) (Icc (0 : ℝ) 1)) ∧
      (∀ a : Prod.fst '' U, ∀ s ∈ Ioo (0 : ℝ) 1, 0 < p (a.val, Q (a.val, s))) := by
  classical
  choose D hdensity hsupport using hex
  obtain ⟨hlower, hupper⟩ := measurable_endpoints_of_open_fibers hU D hsupport
  have hd : Measurable (fun z : (Prod.fst '' U) × ℝ => (D z.1).density z.2) := by
    have heq : (fun z : (Prod.fst '' U) × ℝ => (D z.1).density z.2) =
        (fun z : (Prod.fst '' U) × ℝ => p (z.1.val, z.2)) := by
      funext z
      exact congrFun (hdensity z.1) z.2
    rw [heq]
    exact hp.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨Q, hQ, hmatch, hlaw, hderiv, hstrict⟩ :=
    exists_measurable_quantile_extension (Prod.fst '' U)
      (SectionMeasure.isOpen_projection hU).measurableSet D hlower hupper hd
  refine ⟨Q, hQ, ?_, ?_, ?_, hstrict, ?_⟩
  · intro a
    rw [hlaw a, densityMeasure, hsupport a, hdensity a]
  · intro a s hs
    have hm := (D a).quantileReal_mem_interior hs
    rw [← hmatch a s, hsupport a] at hm
    exact hm
  · intro a s hs
    simpa only [hdensity a] using hderiv a s hs
  · intro a s hs
    have hpos := (D a).positive _ ((D a).quantileReal_mem_interior hs)
    simpa only [hdensity a, ← hmatch a s] using hpos

end PositiveIntervalDensity
end Problem358

end

end OAI
