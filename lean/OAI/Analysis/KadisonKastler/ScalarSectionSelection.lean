import OAI.Analysis.KadisonKastler.ScalarBoundaryMean

namespace OAI

/-! # Selecting a scalar section by a countable measurable coordinate

The rooted random walk evaluates a bounded boundary family at its root.
Countability makes the simultaneous almost-everywhere representative bounds
and linear identities legitimate.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X}
  [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

include hr in
omit [DiscreteTopology G] in
theorem measurable_scalarSectionSelect (F : G →ᵇ ScalarLInfinity μ) :
    Measurable (fun x => F (r x) x) := by
  have hf : Measurable (fun p : G × X => F p.1 p.2) :=
    measurable_from_prod_countable_right (fun g => (Lp.stronglyMeasurable (F g)).measurable)
  exact hf.comp (hr.prodMk measurable_id)

omit [MeasurableSpace G] [MeasurableSingletonClass G] [DiscreteTopology G] in
theorem scalarSectionSelect_ae_bound (F : G →ᵇ ScalarLInfinity μ) :
    ∀ᵐ x ∂μ, ‖F (r x) x‖ ≤ ‖F‖ := by
  filter_upwards [ae_all_iff.mpr (fun g => scalarInfinity_ae_norm_le (F g))] with x hx
  exact (hx (r x)).trans (F.norm_coe_le_norm (r x))

def scalarSectionSelect (F : G →ᵇ ScalarLInfinity μ) : ScalarLInfinity μ :=
  (memLp_top_of_bound (measurable_scalarSectionSelect r hr F).stronglyMeasurable.aestronglyMeasurable
    ‖F‖ (scalarSectionSelect_ae_bound r F)).toLp (fun x => F (r x) x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_ae (F : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr F =ᵐ[μ] fun x => F (r x) x := MemLp.coeFn_toLp _

omit [DiscreteTopology G] in
theorem scalarSectionSelect_add (F K : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr (F + K) = scalarSectionSelect r hr F + scalarSectionSelect r hr K := by
  apply Lp.ext
  filter_upwards [scalarSectionSelect_ae r hr (F + K), scalarSectionSelect_ae r hr F,
    scalarSectionSelect_ae r hr K,
    ae_all_iff.mpr (fun g => Lp.coeFn_add (F g) (K g)),
    Lp.coeFn_add (scalarSectionSelect r hr F) (scalarSectionSelect r hr K)]
    with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha, he, hb, hc]
  exact hd (r x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_smul (c : ℂ) (F : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr (c • F) = c • scalarSectionSelect r hr F := by
  apply Lp.ext
  filter_upwards [scalarSectionSelect_ae r hr (c • F), scalarSectionSelect_ae r hr F,
    ae_all_iff.mpr (fun g => Lp.coeFn_smul c (F g)),
    Lp.coeFn_smul c (scalarSectionSelect r hr F)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha, hd, hb]
  exact hc (r x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_const (f : ScalarLInfinity μ) :
    scalarSectionSelect r hr (BoundedContinuousFunction.const G f) = f :=
  Lp.ext (scalarSectionSelect_ae r hr _)

theorem scalarSectionSelect_module (b : ScalarLInfinity μ) (F : G →ᵇ ScalarLInfinity μ) :
    scalarSectionSelect r hr (scalarBoundaryModule b F) =
      scalarInfinityMul b (scalarSectionSelect r hr F) := by
  apply Lp.ext
  filter_upwards [scalarSectionSelect_ae r hr (scalarBoundaryModule b F),
    scalarSectionSelect_ae r hr F,
    scalarInfinityMul_ae b (scalarSectionSelect r hr F),
    ae_all_iff.mpr (fun g => scalarInfinityMul_ae b (F g))] with x ha hb hc hd
  rw [ha, hc, hb]
  exact hd (r x)

omit [DiscreteTopology G] in
theorem scalarSectionSelect_positive (F : G →ᵇ ScalarLInfinity μ)
    (hF : ∀ g, ∀ᵐ x ∂μ, (F g x).im = 0 ∧ 0 ≤ (F g x).re) :
    ∀ᵐ x ∂μ, (scalarSectionSelect r hr F x).im = 0 ∧
      0 ≤ (scalarSectionSelect r hr F x).re := by
  filter_upwards [scalarSectionSelect_ae r hr F, ae_all_iff.mpr hF] with x hx hfx
  rw [hx]
  exact hfx (r x)

variable [IsProbabilityMeasure μ]

omit [DiscreteTopology G] in
theorem norm_scalarSectionSelect_le (F : G →ᵇ ScalarLInfinity μ) :
    ‖scalarSectionSelect r hr F‖ ≤ ‖F‖ := by
  have hb : ∀ᵐ x ∂μ, ‖scalarSectionSelect r hr F x‖ ≤ ‖F‖ := by
    filter_upwards [scalarSectionSelect_ae r hr F, scalarSectionSelect_ae_bound r F]
      with x hx hf
    rwa [hx]
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg F) hb

def scalarSectionSelectL : (G →ᵇ ScalarLInfinity μ) →L[ℂ] ScalarLInfinity μ :=
  LinearMap.mkContinuous
    { toFun := scalarSectionSelect r hr
      map_add' := scalarSectionSelect_add r hr
      map_smul' := scalarSectionSelect_smul r hr }
    1 (fun F => by simpa using norm_scalarSectionSelect_le r hr F)

end

end KadisonKastler

end OAI
