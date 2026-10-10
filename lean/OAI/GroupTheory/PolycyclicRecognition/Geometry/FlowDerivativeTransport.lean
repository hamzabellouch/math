import OAI.GroupTheory.PolycyclicRecognition.Analysis.HorizontalProfileLabels
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! # Base-point derivatives transported to almost every point of a flow line -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory MeasureTheory.Measure

theorem ae_flow_hasDerivAt_of_ae_base
    {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f q : G → W) (U : Set G)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v))) (q g) 0) :
    ∀ᵐ g ∂μ, ∀ᵐ t : ℝ, g * Exp (t • v) ∈ U →
      HasDerivAt (fun s : ℝ => f (g * Exp (s • v))) (q (g * Exp (t • v))) t := by
  have hpres : MeasurePreserving (fun z : ℝ × G => (z.1, z.2 * Exp (z.1 • v)))
      (volume.prod μ) (volume.prod μ) := by
    exact (MeasurePreserving.id volume).skew_product
      (by
        change Measurable (fun z : ℝ × G => z.2 * Exp (z.1 • v))
        exact (continuous_snd.mul (hExp.comp (continuous_fst.smul continuous_const))).measurable)
      (Eventually.of_forall (fun t => (measurePreserving_mul_right μ (Exp (t • v))).map_eq))
  have hh := hpres.quasiMeasurePreserving.ae (quasiMeasurePreserving_snd.ae hbase)
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae hh
  filter_upwards [ae_ae_of_ae_prod hswap] with g hg
  filter_upwards [hg] with t ht hmem
  change g * Exp (t • v) ∈ U →
    HasDerivAt (fun s : ℝ => f ((g * Exp (t • v)) * Exp (s • v)))
      (q (g * Exp (t • v))) 0 at ht
  have hd := (ht hmem).scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  have heq : (fun s : ℝ => f ((g * Exp (t • v)) * Exp ((s - t) • v))) =
      (fun s : ℝ => f (g * Exp (s • v))) := by
    funext s
    rw [mul_assoc, ← hadd]
    rw [show t + (s - t) = s by ring]
  simpa only [Function.comp_def, Function.id_def, one_smul, heq] using hd

theorem ae_flowLine_hasDerivAt_of_ae_base
    {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f q : G → W) (U : Set G)
    (hbase : ∀ᵐ g ∂μ, g ∈ U → HasDerivAt (fun t : ℝ => f (g * Exp (t • v))) (q g) 0)
    (T : ℝ) :
    ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T → ∀ᵐ t ∂volume.restrict (Icc 0 T),
      HasDerivAt (fun s : ℝ => f (g * Exp (s • v))) (q (g * Exp (t • v))) t := by
  filter_upwards [ae_flow_hasDerivAt_of_ae_base μ Exp hExp hadd v f q U hbase] with g hg hstay
  filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem measurableSet_Icc] with t ht hmem
  exact ht (hstay t hmem)

end PolycyclicRecognition

end

end OAI
