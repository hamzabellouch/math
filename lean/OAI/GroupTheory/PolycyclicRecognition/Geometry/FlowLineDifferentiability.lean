import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowNeighborhoods
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # Almost-everywhere differentiability at base points of horizontal flows -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped NNReal

theorem ae_of_ae_right_translates
    {G T : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableSpace T] (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (ν : Measure T) [SFinite ν] [NeZero ν]
    (F : T → G) (hF : Measurable F) {p : G → Prop}
    (hp : MeasurableSet {g | p g})
    (h : ∀ g, ∀ᵐ t ∂ν, p (g * F t)) : ∀ᵐ g ∂μ, p g := by
  have hm : MeasurableSet {z : G × T | p (z.1 * F z.2)} :=
    hp.preimage (measurable_fst.mul (hF.comp measurable_snd))
  have hswap := (ae_ae_comm (μ := μ) (ν := ν) hm).mp (Eventually.of_forall h)
  obtain ⟨t, ht⟩ := hswap.exists
  have hh := (measurePreserving_mul_right μ (F t)⁻¹).quasiMeasurePreserving.ae ht
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

theorem ae_flowLine_differentiableAt_zero
    {G V W : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (f : G → W) (hf : Continuous f) (Ω : Set G) (hΩ : IsOpen Ω)
    (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (g * Exp (t • v)))
      {t | g * Exp (t • v) ∈ Ω}) :
    ∀ᵐ g ∂μ, g ∈ Ω → DifferentiableAt ℝ (fun t : ℝ => f (g * Exp (t • v))) 0 := by
  let curve := fun (g : G) (t : ℝ) => f (g * Exp (t • v))
  have hc : Continuous curve.uncurry := by
    change Continuous (fun z : G × ℝ => f (z.1 * Exp (z.2 • v)))
    fun_prop
  have hm : MeasurableSet {g : G | g ∈ Ω → DifferentiableAt ℝ (curve g) 0} := by
    have hd := measurableSet_of_differentiableAt_with_param ℝ hc
    have hd0 := hd.preimage (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
    convert hΩ.measurableSet.compl.union hd0 using 1
    ext g
    simp only [mem_union, mem_compl_iff, mem_preimage, mem_ofPred_eq,
      Function.id_def, imp_iff_not_or]
  apply ae_of_ae_right_translates μ volume (fun t : ℝ => Exp (t • v))
    ((hExp.comp (continuous_id.smul continuous_const)).measurable) hm
  intro g
  have ho : IsOpen {t : ℝ | g * Exp (t • v) ∈ Ω} :=
    hΩ.preimage (by fun_prop)
  filter_upwards [(hlip g).ae_differentiableWithinAt_of_mem (μ := volume)] with t ht htΩ
  have hd := (ht htΩ).differentiableAt (ho.mem_nhds htΩ)
  have hd' : DifferentiableAt ℝ (curve g) (t + 0) := by simpa [curve] using hd
  have hcomp := hd'.comp (0 : ℝ) (differentiableAt_id.const_add t)
  have heq : curve (g * Exp (t • v)) = fun s : ℝ => curve g (t + s) := by
    funext s
    dsimp [curve]
    rw [mul_assoc, ← hadd]
  rwa [heq]

end PolycyclicRecognition

end

end OAI
