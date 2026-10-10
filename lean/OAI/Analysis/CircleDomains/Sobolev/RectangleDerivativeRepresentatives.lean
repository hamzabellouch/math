import OAI.Analysis.CircleDomains.Sobolev.MeasurableLineDerivatives
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Prod

namespace OAI

/-! Measurable representatives of the two ACL derivatives in a physical
rectangle. The null set is chosen before slicing, and exceptional lines
are discarded only after applying Fubini. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem ae_mem_Ioo_of_Icc (a b : ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Ioo a b := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff]] with x hxa hxb hx
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩

theorem lineDeriv_horizontal (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (1, 0) = deriv (fun t => f (t, p.2)) p.1 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (t, y)) x 0

theorem lineDeriv_vertical (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    lineDeriv ℝ f p (0, 1) = deriv (fun t => f (p.1, t)) p.2 := by
  rcases p with ⟨x, y⟩
  simp only [lineDeriv, Prod.smul_mk, smul_eq_mul, mul_one, mul_zero,
    Prod.mk_add_mk, add_zero]
  simpa only [add_zero] using deriv_comp_const_add (fun t => f (x, t)) y 0

theorem exists_measurable_horizontal_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ y ∂volume.restrict (Icc c d),
      AbsolutelyContinuousOnInterval (fun x => f (x, y)) a b) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b),
        G (x, y) = deriv (fun t => f (t, y)) x := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (1, 0) hf
  have hrep' : ∀ᵐ y ∂volume, ∀ᵐ x ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (1, 0) →
        G (x, y) = lineDeriv ℝ f (x, y) (1, 0) := by
    have hr := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae (by
        simpa only [Measure.volume_eq_prod] using hrep)
    exact Measure.ae_ae_of_ae_prod hr
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc c d, ae_restrict_of_ae hrep'] with y hy hyI hyr
  filter_upwards [ae_mem_Ioo_of_Icc a b,
    ae_restrict_of_ae hy.ae_differentiableAt, ae_restrict_of_ae hyr] with x hxI hxd hxr
  have hd := hxd (Icc_subset_uIcc ⟨hxI.1.le, hxI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (1, 0) := by
    have h : HasDerivAt (fun t => f (t, y)) (deriv (fun t => f (t, y)) x) (x + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add x 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hxr ⟨hxI, hyI⟩ hline).trans (lineDeriv_horizontal f (x, y))

theorem exists_measurable_vertical_derivative
    (f : ℝ × ℝ → ℝ) {a b c d : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo a b ×ˢ Ioo c d)))
    (hac : ∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => f (x, y)) c d) :
    ∃ G : ℝ × ℝ → ℝ, Measurable G ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d),
        G (x, y) = deriv (fun t => f (x, t)) y := by
  let : Measure.IsAddRightInvariant (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  obtain ⟨G, hG, hrep⟩ := exists_measurable_lineDeriv_representative
    (isOpen_Ioo.prod isOpen_Ioo) (0, 1) hf
  have hrep' : ∀ᵐ x ∂volume, ∀ᵐ y ∂volume,
      (x, y) ∈ Ioo a b ×ˢ Ioo c d → LineDifferentiableAt ℝ f (x, y) (0, 1) →
        G (x, y) = lineDeriv ℝ f (x, y) (0, 1) :=
    Measure.ae_ae_of_ae_prod (by simpa only [Measure.volume_eq_prod] using hrep)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hac, ae_mem_Ioo_of_Icc a b, ae_restrict_of_ae hrep'] with x hx hxI hxr
  filter_upwards [ae_mem_Ioo_of_Icc c d,
    ae_restrict_of_ae hx.ae_differentiableAt, ae_restrict_of_ae hxr] with y hyI hyd hyr
  have hd := hyd (Icc_subset_uIcc ⟨hyI.1.le, hyI.2.le⟩)
  have hline : LineDifferentiableAt ℝ f (x, y) (0, 1) := by
    have h : HasDerivAt (fun t => f (x, t)) (deriv (fun t => f (x, t)) y) (y + 0) := by
      simpa only [add_zero] using hd.hasDerivAt
    have ht := h.comp_const_add y 0
    simpa only [LineDifferentiableAt, Prod.smul_mk, smul_eq_mul, mul_one,
      mul_zero, Prod.mk_add_mk, add_zero] using ht.differentiableAt
  exact (hyr ⟨hxI, hyI⟩ hline).trans (lineDeriv_vertical f (x, y))

end CircleDomainRigidity

end

end OAI
