import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowDerivativeTransport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.GenericLipschitzProfile

namespace OAI

/-! # Generic flow restrictions have one image chamber almost everywhere -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open Set Filter MeasureTheory
open scoped NNReal

theorem ae_generic_flowLine_chamber_agreement
    {G V W I B L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (hweights : ∀ i, D.weight i ≠ 0)
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (π : V →L[ℝ] W) (v : V) (hw : ∀ i, D.weight i (π v) ≠ 0)
    (f : G → W) (hf : Continuous f) (U : Set G)
    (label : G → L) (A : L → templateSymmetryGroup D)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v)))
      ((A (label g)).val (π v)) 0)
    {T : ℝ} (hT : 0 ≤ T) (C : ℝ≥0)
    (hlip : ∀ g ∈ flowLineBase U Exp v T,
      LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v))) (Icc 0 T))
    (hvol : ∀ g ∈ flowLineBase U Exp v T,
      T * D.segmentSupport (π v) ≤ D.templateSupport ((fun t : ℝ => f (g * Exp (t • v))) '' Icc 0 T)) :
    ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
        (A (label (g * Exp (s • v)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
              (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) =
          (A (label (g * Exp (t • v)))).val ''
            closedWeightChamber (fun i => (D.weight i).toContinuousLinearMap)
              (weightSigns (fun i => (D.weight i).toContinuousLinearMap) (π v)) := by
  filter_upwards [ae_flowLine_hasDerivAt_of_ae_base μ Exp hExp hadd v f
    (fun g => (A (label g)).val (π v)) U hbase T] with g hg hstay
  let c : ℝ → W := fun t => f (g * Exp (t • v))
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hdc : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      HasDerivAt (fun s : ℝ => c s - f g) ((A (label (g * Exp (t • v)))).val (π v)) t := by
    filter_upwards [hg hstay] with t ht
    exact ht.sub_const (f g)
  have hvol' : T * D.segmentSupport (π v) ≤
      D.templateSupport ((fun t : ℝ => c t - f g) '' Icc 0 T) := by
    have hcpt : IsCompact (c '' Icc 0 T) := isCompact_Icc.image hc
    have hne : (c '' Icc 0 T).Nonempty := (nonempty_Icc.mpr hT).image c
    have heq : (fun t : ℝ => c t - f g) '' Icc 0 T =
        (fun x : W => x + (-f g)) '' (c '' Icc 0 T) := by
      rw [image_image]
      simp only [sub_eq_add_neg]
    rw [heq, D.templateSupport_translate hcpt hne (-f g)]
    exact hvol g hstay
  have hlip' : LipschitzOnWith C (fun t : ℝ => c t - f g) (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [dist_sub_right, c] using (hlip g hstay).dist_le_mul s hs t ht
  exact D.generic_lipschitz_profile_chamber_agreement hweights (fun t => c t - f g)
    (hc.sub continuous_const) (by simp [c, hzero]) (π v) hw hT
    hlip' (fun t => A (label (g * Exp (t • v)))) hdc hvol'

end PolycyclicRecognition.SupportDatum

end

end OAI
