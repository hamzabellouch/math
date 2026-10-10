import OAI.Geometry.RCD.Metric.L2IntegralRepresentative

namespace OAI

/-! # Pointwise representation of a bounded compact-support L2 integral -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem bounded_support_L2_integral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [IsFiniteMeasure ν]
    {s : Set X} (hs : MeasurableSet s) (hfin : μ s ≠ ∞)
    (u : Y → Lp ℝ 2 μ) (hu : Integrable u ν) (f : Y → X → ℝ)
    (hf : StronglyMeasurable (Function.uncurry f))
    (hr : ∀ᵐ y ∂ν, u y =ᵐ[μ] f y) {A : ℝ}
    (hb : ∀ᵐ y ∂ν, ∀ x, |f y x| ≤ A) (hz : ∀ᵐ y ∂ν, ∀ x, x ∉ s → f y x = 0) :
    MemLp (fun x => ∫ y, f y x ∂ν) 2 μ ∧
      (∫ y, u y ∂ν) =ᵐ[μ] fun x => ∫ y, f y x ∂ν := by
  let g := fun x => ∫ y, f y x ∂ν
  have hg0 (x : X) (hx : x ∉ s) : g x = 0 := by
    exact integral_eq_zero_of_ae (hz.mono fun y hy => hy x hx)
  have hgb (x : X) : ‖g x‖ ≤ A*ν.real univ :=
    norm_integral_le_of_norm_le_const
      (hb.mono fun y hy => by simpa only [Real.norm_eq_abs] using hy x)
  have hgm : StronglyMeasurable g := hf.integral_prod_left
  have hg : MemLp g 2 μ := by
    let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hfin.lt_top⟩
    have hg' : MemLp g 2 (μ.restrict s) :=
      MemLp.of_bound hgm.aestronglyMeasurable.restrict _ (Eventually.of_forall hgb)
    have he : s.indicator g = g := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx,hg0]
    rw [← he]
    exact (memLp_indicator_iff_restrict hs).mpr hg'
  refine ⟨hg,L2_integral_representative μ ν u hu f hr ?_ g hg (EventuallyEq.refl _ _)⟩
  intro ξ
  let w := s.indicator (fun x => |ξ x|)
  have hwi : Integrable w μ :=
    (integrable_indicator_iff hs).mpr (lp_integrableOn_of_finite μ ξ s hfin).abs
  have hbase : Integrable (fun q : Y × X => (1:ℝ)*w q.2) (ν.prod μ) :=
    (integrable_const (1:ℝ)).mul_prod hwi
  have hm : AEStronglyMeasurable (fun q : Y × X => ξ q.2*f q.1 q.2) (ν.prod μ) :=
    ((Lp.stronglyMeasurable ξ).comp_measurable measurable_snd).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply (hbase.const_mul A).mono' hm
  have hpair : ∀ᵐ q ∂ν.prod μ, (∀ x, |f q.1 x| ≤ A) ∧
      (∀ x, x ∉ s → f q.1 x = 0) :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (hb.and hz)
  filter_upwards [hpair] with q hq
  rcases hq with ⟨hb,hz⟩
  change ‖ξ q.2*f q.1 q.2‖ ≤ A*((1:ℝ)*w q.2)
  by_cases hx : q.2 ∈ s
  · simp only [Real.norm_eq_abs,abs_mul,w,indicator_of_mem hx,one_mul]
    exact (mul_le_mul_of_nonneg_left (hb q.2) (abs_nonneg _)).trans_eq (mul_comm _ _)
  · simp only [hz q.2 hx,mul_zero,norm_zero,w,indicator_of_notMem hx,le_refl]

end RegularPointCoordinates

end

end OAI
