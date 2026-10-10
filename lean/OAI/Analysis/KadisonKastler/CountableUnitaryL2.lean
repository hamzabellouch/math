import OAI.Analysis.KadisonKastler.HilbertVariance
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! Isometric multiplication in L2 by a countable measurable unitary field. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X G K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem countableUnitaryAction_aestronglyMeasurable
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    {f : X → K} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (U (c x) : K →L[ℂ] K) (f x)) μ := by
  borelize K
  have hm : Measurable (fun p : G × K => (U p.1 : K →L[ℂ] K) p.2) :=
    measurable_from_prod_countable_right (fun g => (U g : K →L[ℂ] K).continuous.measurable)
  exact (hm.comp_aemeasurable (hc.aemeasurable.prodMk hf.aemeasurable)).aestronglyMeasurable

theorem countableUnitaryAction_memLp
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    {f : X → K} (hf : MemLp f 2 μ) :
    MemLp (fun x => (U (c x) : K →L[ℂ] K) (f x)) 2 μ :=
  hf.congr_norm (countableUnitaryAction_aestronglyMeasurable U hc hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (Unitary.norm_map (U (c x)) (f x)).symm)

def countableUnitaryL2 (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : Measurable c)
    (f : Lp K 2 μ) : Lp K 2 μ :=
  (countableUnitaryAction_memLp U hc (Lp.memLp f)).toLp _

theorem countableUnitaryL2_ae (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f : Lp K 2 μ) :
    countableUnitaryL2 U hc f =ᵐ[μ] fun x => (U (c x) : K →L[ℂ] K) (f x) :=
  MemLp.coeFn_toLp _

theorem countableUnitaryL2_norm (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f : Lp K 2 μ) : ‖countableUnitaryL2 U hc f‖ = ‖f‖ := by
  rw [countableUnitaryL2, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae
    (countableUnitaryAction_aestronglyMeasurable U hc (Lp.aestronglyMeasurable f))
    (Lp.aestronglyMeasurable f) (Filter.Eventually.of_forall fun x => Unitary.norm_map _ _)

theorem countableUnitaryL2_sub (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f g : Lp K 2 μ) :
    countableUnitaryL2 U hc (f - g) = countableUnitaryL2 U hc f - countableUnitaryL2 U hc g := by
  apply Lp.ext
  filter_upwards [countableUnitaryL2_ae U hc (f - g), countableUnitaryL2_ae U hc f,
    countableUnitaryL2_ae U hc g, Lp.coeFn_sub f g,
    Lp.coeFn_sub (countableUnitaryL2 U hc f) (countableUnitaryL2 U hc g)] with x h h₁ h₂ hs ht
  rw [h, ht, hs, Pi.sub_apply, Pi.sub_apply, h₁, h₂, map_sub]

theorem countableUnitaryL2_inv (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable c) (f : Lp K 2 μ) :
    countableUnitaryL2 (fun g => (U g)⁻¹) hc (countableUnitaryL2 U hc f) = f := by
  apply Lp.ext
  filter_upwards [countableUnitaryL2_ae (fun g => (U g)⁻¹) hc (countableUnitaryL2 U hc f),
    countableUnitaryL2_ae U hc f] with x h₁ h₂
  rw [h₁, h₂]
  exact (Unitary.linearIsometryEquiv (U (c x))).symm_apply_apply (f x)

end

end KadisonKastler

end OAI
