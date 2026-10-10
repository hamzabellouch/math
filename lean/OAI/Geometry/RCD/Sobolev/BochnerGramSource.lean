import OAI.Geometry.RCD.Sobolev.BochnerProductDensity
import OAI.Geometry.RCD.Metric.LocalMeasureProduct
import OAI.Geometry.RCD.Sobolev.SignedTestFunctional

namespace OAI

/-! # Integrating the full sources in the Gram product equation -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Full source of a Gram entry with its Bochner measure separated out. -/
def bochnerGramSource (K : ℝ) (f g df dg : SobolevSpace μ hQ)
    (S : SignedMeasure X) : SignedMeasure X :=
  (2 : ℝ) • S+μ.withDensityᵥ (bochnerDrift μ hQ K f g df dg)

omit [ProperSpace X] in
theorem integral_bochnerGramSource (K : ℝ) (f g df dg : SobolevSpace μ hQ)
    (S : SignedMeasure X) (q : X →ᵇ ℝ) :
    signedTestIntegral q (bochnerGramSource μ hQ K f g df dg S) =
      2*signedTestIntegral q S+(∫ x, q x*bochnerDrift μ hQ K f g df dg x ∂μ) := by
  change (∫ᵛ x, q x ∂<•((2 : ℝ) • S+μ.withDensityᵥ (bochnerDrift μ hQ K f g df dg))) = _
  rw [VectorMeasure.integral_add_vectorMeasure (PositiveBilinearMeasure.integrable_weight q _)
    (PositiveBilinearMeasure.integrable_weight q _),VectorMeasure.integral_smul_vectorMeasure,
    integral_signedDensity μ (bochnerDrift_integrable μ hQ K f g df dg)]
  rfl

omit [ProperSpace X] in
theorem integral_cutoffMeasureSource (g c : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (ν : SignedMeasure X) (χ q : X →ᵇ ℝ) :
    signedTestIntegral q (cutoffMeasureSource μ hQ g c d ν χ) =
      signedTestIntegral (q*χ) ν+(∫ x, q x*cutoffSourceDensity μ hQ g c d x ∂μ) := by
  change (∫ᵛ x, q x ∂<•(signedSourceWeight ν χ+μ.withDensityᵥ (cutoffSourceDensity μ hQ g c d))) = _
  rw [VectorMeasure.integral_add_vectorMeasure (PositiveBilinearMeasure.integrable_weight q _)
    (PositiveBilinearMeasure.integrable_weight q _),integral_signedSourceWeight,
    integral_signedDensity μ (cutoffSourceDensity_integrable μ hQ g c d)]
  rfl


omit [ProperSpace X] in
/-- A compactly supported test sees only the local L² source. -/
theorem integral_cutoffMeasureSource_local {Ω : Set X} (hΩ : MeasurableSet Ω)
    (g c : SobolevSpace μ hQ) (d e : Lp ℝ 2 μ) (ν : SignedMeasure X)
    (χ q : X →ᵇ ℝ) (hqs : tsupport q ⊆ Ω) (hde : d =ᵐ[μ.restrict Ω] e) :
    signedTestIntegral q (cutoffMeasureSource μ hQ g c d ν χ) =
      signedTestIntegral q (cutoffMeasureSource μ hQ g c e ν χ) := by
  rw [integral_cutoffMeasureSource,integral_cutoffMeasureSource]
  congr 1
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hΩ).mp hde] with x hx
  by_cases hm : x ∈ Ω
  · dsimp only [cutoffSourceDensity]
    rw [hx hm]
  · have hz : q x=0 := image_eq_zero_of_notMem_tsupport (fun hs => hm (hqs hs))
    simp only [hz,zero_mul]

omit [ProperSpace X] in
/-- The two full product sources combine to the integrable drift density.
The Bochner parts keep their actual signed measures. -/
theorem integral_gramProductSource (K : ℝ)
    (f g h df dg dh Fg Fh : SobolevSpace μ hQ)
    (Sg Sh : SignedMeasure X) (G H q : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ g =ᵐ[μ] G)
    (hH : SobolevSpace.toLp μ hQ h =ᵐ[μ] H) :
    signedTestIntegral q
      (cutoffMeasureSource μ hQ Fh g (SobolevSpace.toLp μ hQ dg)
        (bochnerGramSource μ hQ K f h df dh Sh) G+
      cutoffMeasureSource μ hQ Fg h (SobolevSpace.toLp μ hQ dh)
        (bochnerGramSource μ hQ K f g df dg Sg) H) =
      2*signedTestIntegral (q*G) Sh+2*signedTestIntegral (q*H) Sg+
        (∫ x, q x*bochnerProductDensity μ hQ K f g h df dg dh Fg Fh x ∂μ) := by
  rw [map_add,integral_cutoffMeasureSource,integral_cutoffMeasureSource,
    integral_bochnerGramSource,integral_bochnerGramSource]
  let a : X → ℝ := fun x => G x*bochnerDrift μ hQ K f h df dh x
  let b := cutoffSourceDensity μ hQ Fh g (SobolevSpace.toLp μ hQ dg)
  let c : X → ℝ := fun x => H x*bochnerDrift μ hQ K f g df dg x
  let d := cutoffSourceDensity μ hQ Fg h (SobolevSpace.toLp μ hQ dh)
  have ha : Integrable a μ := (bochnerDrift_integrable μ hQ K f h df dh).bdd_mul
    G.continuous.aestronglyMeasurable (Eventually.of_forall G.norm_coe_le_norm)
  have hb : Integrable b μ := cutoffSourceDensity_integrable μ hQ Fh g _
  have hc : Integrable c μ := (bochnerDrift_integrable μ hQ K f g df dg).bdd_mul
    H.continuous.aestronglyMeasurable (Eventually.of_forall H.norm_coe_le_norm)
  have hd : Integrable d μ := cutoffSourceDensity_integrable μ hQ Fg h _
  have hqa := ha.bdd_mul q.continuous.aestronglyMeasurable (Eventually.of_forall q.norm_coe_le_norm)
  have hqb := hb.bdd_mul q.continuous.aestronglyMeasurable (Eventually.of_forall q.norm_coe_le_norm)
  have hqc := hc.bdd_mul q.continuous.aestronglyMeasurable (Eventually.of_forall q.norm_coe_le_norm)
  have hqd := hd.bdd_mul q.continuous.aestronglyMeasurable (Eventually.of_forall q.norm_coe_le_norm)
  have heq : (∫ x, q x*bochnerProductDensity μ hQ K f g h df dg dh Fg Fh x ∂μ) =
      (∫ x, q x*a x ∂μ)+(∫ x, q x*b x ∂μ)+
        (∫ x, q x*c x ∂μ)+(∫ x, q x*d x ∂μ) := by
    have he : (fun x => q x*bochnerProductDensity μ hQ K f g h df dg dh Fg Fh x) =ᵐ[μ]
        fun x => (q x*a x+q x*b x)+(q x*c x+q x*d x) := by
      filter_upwards [hG,hH] with x hx hy
      dsimp only [bochnerProductDensity,a,b,c,d,cutoffSourceDensity]
      rw [hx,hy]
      ring
    have hab : Integrable (fun x => q x*a x+q x*b x) μ := hqa.add hqb
    have hcd : Integrable (fun x => q x*c x+q x*d x) μ := hqc.add hqd
    rw [integral_congr_ae he,integral_add hab hcd,
      integral_add hqa hqb,integral_add hqc hqd]
    ring
  have hqa' : (∫ x, (q*G) x*bochnerDrift μ hQ K f h df dh x ∂μ) = ∫ x, q x*a x ∂μ := by
    congr 1
    funext x
    change (q x*G x)*_ = q x*(G x*_)
    ring
  have hqc' : (∫ x, (q*H) x*bochnerDrift μ hQ K f g df dg x ∂μ) = ∫ x, q x*c x ∂μ := by
    congr 1
    funext x
    change (q x*H x)*_ = q x*(H x*_)
    ring
  rw [hqa',hqc',heq]
  ring

end RegularPointCoordinates

end

end OAI
