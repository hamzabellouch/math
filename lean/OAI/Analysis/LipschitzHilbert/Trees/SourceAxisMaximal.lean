import OAI.Analysis.LipschitzHilbert.Trees.SourceGlobalDyadicMaximal
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The actual one-coordinate dyadic maximal operator on the plane.
Fubini transfers the uniform line estimate without a dimension or scale
count factor. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def horizontalCellMean (q k : ℤ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  cellMean q k (fun x => f (x,z.2)) z.1

def horizontalMaximal (q top : ℤ) (N : ℕ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  dyadicMaximal q top N (fun x => f (x,z.2)) z.1

theorem indexedCellIntegral_measurable (q k : ℤ) {f : ℝ×ℝ → ℝ}
    (hf : Measurable f) :
    Measurable (fun p : ℤ×ℝ => (∫ x in cell q k p.1, f (x,p.2))/scale k) := by
  apply measurable_from_prod_countable_right
  intro i
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ:=volume.restrict (cell q k i))).measurable.div_const _

theorem horizontalCellMean_measurable (q k : ℤ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (horizontalCellMean q k f) := by
  change Measurable (fun z : ℝ×ℝ =>
    (∫ x in cell q k (index q k z.1), f (x,z.2))/scale k)
  have hm1 : Measurable (fun z : ℝ×ℝ => index q k z.1) :=
    (index_measurable q k).comp (measurable_fst : Measurable (Prod.fst : ℝ×ℝ → ℝ))
  have hm : Measurable (fun z : ℝ×ℝ => (index q k z.1,z.2)) :=
    hm1.prodMk (measurable_snd : Measurable (Prod.snd : ℝ×ℝ → ℝ))
  have hprod : Measurable (fun p : ℤ×ℝ =>
      (∫ x in cell q k p.1, f (x,p.2))/scale k) :=
    indexedCellIntegral_measurable (f:=f) q k hf
  have hc := hprod.comp hm
  exact hc

theorem horizontalMaximal_measurable (q top : ℤ) (N : ℕ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (horizontalMaximal q top N f) := by
  exact finiteMaxSignal_measurable (fun n => horizontalCellMean q (top-(n:ℤ)) f) N
    (fun n _ => horizontalCellMean_measurable q (top-(n:ℤ)) hf)

/-- The horizontal maximal operator has squared L² norm at most four
on the product Lebesgue measure. -/
theorem horizontalMaximal_energy (q top : ℤ) (N : ℕ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (horizontalMaximal q top N f) 2 (volume.prod volume) ∧
    (∫ z, (horizontalMaximal q top N f z)^2 ∂volume.prod volume) ≤
      4*∫ z, (f z)^2 ∂volume.prod volume := by
  let H := horizontalMaximal q top N f
  have hHm : Measurable H := horizontalMaximal_measurable q top N hfmeas
  have hfm : Integrable (fun z => (f z)^2) (volume.prod volume) := hf.integrable_sq
  have hslices : ∀ᵐ y ∂volume, MemLp (fun x => f (x,y)) 2 volume := by
    filter_upwards [hfm.prod_left_ae] with y hy
    exact (memLp_two_iff_integrable_sq
      (hfmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hy
  have hinner : ∀ᵐ y ∂volume,
      Integrable (fun x => (H (x,y))^2) volume ∧
      (∫ x, (H (x,y))^2) ≤ 4*∫ x, (f (x,y))^2 := by
    filter_upwards [hslices] with y hy
    have h := dyadicMaximal_energy q top N hy
    exact ⟨h.1.integrable_sq,h.2⟩
  have hmajor : Integrable (fun y => 4*∫ x, (f (x,y))^2) volume :=
    hfm.integral_prod_right.const_mul 4
  have houter : Integrable (fun y => ∫ x, ‖(H (x,y))^2‖) volume := by
    apply hmajor.mono' (hHm.pow_const 2).stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hinner] with y hy
    have hn : (∫ x, ‖(H (x,y))^2‖) = ∫ x, (H (x,y))^2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => Real.norm_of_nonneg (sq_nonneg (H (x,y))))
    rw [hn, Real.norm_of_nonneg (integral_nonneg (fun x => sq_nonneg (H (x,y))))]
    exact hy.2
  have hHi : Integrable (fun z => (H z)^2) (volume.prod volume) :=
    (integrable_prod_iff' (hHm.pow_const 2).aestronglyMeasurable).mpr
      ⟨hinner.mono (fun _ hy => hy.1),houter⟩
  refine ⟨(memLp_two_iff_integrable_sq hHm.aestronglyMeasurable).mpr hHi,?_⟩
  rw [integral_prod_symm _ hHi,integral_prod_symm _ hfm,←integral_const_mul]
  apply integral_mono_ae hHi.integral_prod_right hmajor
  exact hinner.mono (fun _ hy => hy.2)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
