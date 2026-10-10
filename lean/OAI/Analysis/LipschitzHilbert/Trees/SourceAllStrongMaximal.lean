import OAI.Analysis.LipschitzHilbert.Trees.SourceAllDyadicMaximal

namespace OAI

/-! Countable-scale coordinate maximal functions on the plane, with
uniform strong L² control. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def allHorizontalMaximal (q : ℤ) (f : ℝ×ℝ → ℝ) : ℝ×ℝ → ℝ :=
  monotoneMaximal (fun N : ℕ => horizontalMaximal q (N:ℤ) (2*N) f)

def allVerticalMaximal (q : ℤ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  allHorizontalMaximal q (f ∘ Prod.swap) z.swap

def allStrongMaximal (qx qy : ℤ) (f : ℝ×ℝ → ℝ) : ℝ×ℝ → ℝ :=
  allHorizontalMaximal qx (allVerticalMaximal qy f)

theorem allHorizontalMaximal_measurable (q : ℤ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (allHorizontalMaximal q f) :=
  monotoneMaximal_measurable _ (fun N => horizontalMaximal_measurable q N (2*N) hf)

theorem allVerticalMaximal_measurable (q : ℤ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (allVerticalMaximal q f) :=
  (allHorizontalMaximal_measurable q (hf.comp measurable_swap)).comp measurable_swap

theorem allStrongMaximal_measurable (qx qy : ℤ) {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (allStrongMaximal qx qy f) :=
  allHorizontalMaximal_measurable qx (allVerticalMaximal_measurable qy hf)

theorem allHorizontalMaximal_nonneg (q : ℤ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤allHorizontalMaximal q f z := Real.sqrt_nonneg _

theorem allVerticalMaximal_nonneg (q : ℤ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤allVerticalMaximal q f z := Real.sqrt_nonneg _

theorem allStrongMaximal_nonneg (qx qy : ℤ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤allStrongMaximal qx qy f z := Real.sqrt_nonneg _

theorem allHorizontalMaximal_energy (q : ℤ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (allHorizontalMaximal q f) 2 (volume.prod volume) ∧
    (∫ z, (allHorizontalMaximal q f z)^2 ∂volume.prod volume)≤
      4*∫ z, (f z)^2 ∂volume.prod volume ∧
    ∀ᵐ z ∂volume.prod volume, ∀ k : ℤ,
      |horizontalCellMean q k f z|≤allHorizontalMaximal q f z := by
  have h := monotoneMaximal_energy (volume.prod volume)
    (fun N : ℕ => horizontalMaximal q (N:ℤ) (2*N) f)
    (4*∫ z, (f z)^2 ∂volume.prod volume)
    (mul_nonneg (by norm_num) (integral_nonneg (fun z => sq_nonneg (f z))))
    (fun N => horizontalMaximal_measurable q N (2*N) hfmeas)
    (fun N z => horizontalMaximal_nonneg q N (2*N) f z)
    (fun i j hij z => dyadicWindow_mono q (fun x => f (x,z.2)) hij z.1)
    (fun N => (horizontalMaximal_energy q N (2*N) hfmeas hf).1)
    (fun N => (horizontalMaximal_energy q N (2*N) hfmeas hf).2)
  refine ⟨h.1,h.2.1,?_⟩
  filter_upwards [h.2.2] with z hz
  intro k
  exact (cellMean_le_window q k (fun x => f (x,z.2)) z.1).trans (hz k.natAbs)

theorem allVerticalMaximal_energy (q : ℤ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (allVerticalMaximal q f) 2 (volume.prod volume) ∧
    (∫ z, (allVerticalMaximal q f z)^2 ∂volume.prod volume)≤
      4*∫ z, (f z)^2 ∂volume.prod volume := by
  have hs : MemLp (f ∘ Prod.swap) 2 (volume.prod volume) :=
    hf.comp_measurePreserving Measure.measurePreserving_swap
  have h := allHorizontalMaximal_energy q (hfmeas.comp measurable_swap) hs
  refine ⟨h.1.comp_measurePreserving Measure.measurePreserving_swap,?_⟩
  change (∫ z, (allHorizontalMaximal q (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume)≤_
  rw [show (∫ z, (allHorizontalMaximal q (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume)=
      ∫ z, (allHorizontalMaximal q (f ∘ Prod.swap) z)^2 ∂volume.prod volume from
    integral_prod_swap (fun z => (allHorizontalMaximal q (f ∘ Prod.swap) z)^2)]
  calc
    _ ≤ 4*∫ z, ((f ∘ Prod.swap) z)^2 ∂volume.prod volume := h.2.1
    _ = _ := by
      congr 1
      exact integral_prod_swap (fun z => (f z)^2)

/-- Strong dyadic L² control at every integer scale, with no finite
truncation remaining in the statement. -/
theorem allStrongMaximal_energy (qx qy : ℤ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (allStrongMaximal qx qy f) 2 (volume.prod volume) ∧
    (∫ z, (allStrongMaximal qx qy f z)^2 ∂volume.prod volume)≤
      16*∫ z, (f z)^2 ∂volume.prod volume := by
  have hv := allVerticalMaximal_energy qy hfmeas hf
  have hh := allHorizontalMaximal_energy qx (allVerticalMaximal_measurable qy hfmeas) hv.1
  refine ⟨hh.1,hh.2.1.trans ?_⟩
  calc
    _ ≤ 4*(4*∫ z, (f z)^2 ∂volume.prod volume) := mul_le_mul_of_nonneg_left hv.2 (by norm_num)
    _ = _ := by ring

end LipschitzHilbert.DyadicLineGrid

end

end OAI
