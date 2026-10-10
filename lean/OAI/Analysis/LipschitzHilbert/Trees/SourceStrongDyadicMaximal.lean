import OAI.Analysis.LipschitzHilbert.Trees.SourceAxisMaximal

namespace OAI

/-! Finite rectangular maximal averages on the actual nested line grids.
The constants are uniform in both scale cutoffs. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.DyadicLineGrid

def verticalMaximal (q top : ℤ) (N : ℕ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) : ℝ :=
  horizontalMaximal q top N (f ∘ Prod.swap) z.swap

def strongDyadicMaximal (qx qy topx topy : ℤ) (Nx Ny : ℕ)
    (f : ℝ×ℝ → ℝ) : ℝ×ℝ → ℝ :=
  horizontalMaximal qx topx Nx (verticalMaximal qy topy Ny f)

theorem verticalMaximal_measurable (q top : ℤ) (N : ℕ)
    {f : ℝ×ℝ → ℝ} (hf : Measurable f) : Measurable (verticalMaximal q top N f) :=
  (horizontalMaximal_measurable q top N (hf.comp measurable_swap)).comp measurable_swap

theorem strongDyadicMaximal_measurable (qx qy topx topy : ℤ) (Nx Ny : ℕ)
    {f : ℝ×ℝ → ℝ} (hf : Measurable f) :
    Measurable (strongDyadicMaximal qx qy topx topy Nx Ny f) :=
  horizontalMaximal_measurable qx topx Nx (verticalMaximal_measurable qy topy Ny hf)

theorem verticalMaximal_energy (q top : ℤ) (N : ℕ) {f : ℝ×ℝ → ℝ}
    (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (verticalMaximal q top N f) 2 (volume.prod volume) ∧
    (∫ z, (verticalMaximal q top N f z)^2 ∂volume.prod volume) ≤
      4*∫ z, (f z)^2 ∂volume.prod volume := by
  have hs : MemLp (f ∘ Prod.swap) 2 (volume.prod volume) :=
    hf.comp_measurePreserving Measure.measurePreserving_swap
  have h := horizontalMaximal_energy q top N (hfmeas.comp measurable_swap) hs
  refine ⟨h.1.comp_measurePreserving Measure.measurePreserving_swap,?_⟩
  change (∫ z, (horizontalMaximal q top N (f ∘ Prod.swap) z.swap)^2 ∂volume.prod volume) ≤ _
  rw [show (∫ z, (horizontalMaximal q top N (f ∘ Prod.swap) z.swap)^2
      ∂volume.prod volume) =
      ∫ z, (horizontalMaximal q top N (f ∘ Prod.swap) z)^2 ∂volume.prod volume from
    integral_prod_swap (fun z => (horizontalMaximal q top N (f ∘ Prod.swap) z)^2)]
  calc
    _ ≤ 4*∫ z, ((f ∘ Prod.swap) z)^2 ∂volume.prod volume := h.2
    _ = _ := by
      congr 1
      exact integral_prod_swap (fun z => (f z)^2)

/-- The composition of the two actual dyadic maximal operators has
squared L² norm at most sixteen, independently of the number of scales. -/
theorem strongDyadicMaximal_energy (qx qy topx topy : ℤ) (Nx Ny : ℕ)
    {f : ℝ×ℝ → ℝ} (hfmeas : Measurable f) (hf : MemLp f 2 (volume.prod volume)) :
    MemLp (strongDyadicMaximal qx qy topx topy Nx Ny f) 2 (volume.prod volume) ∧
    (∫ z, (strongDyadicMaximal qx qy topx topy Nx Ny f z)^2 ∂volume.prod volume) ≤
      16*∫ z, (f z)^2 ∂volume.prod volume := by
  have hv := verticalMaximal_energy qy topy Ny hfmeas hf
  have hh := horizontalMaximal_energy qx topx Nx
    (verticalMaximal_measurable qy topy Ny hfmeas) hv.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ 4*(4*∫ z, (f z)^2 ∂volume.prod volume) := mul_le_mul_of_nonneg_left hv.2 (by norm_num)
    _ = _ := by ring

theorem abs_cellMean_le_dyadicMaximal (q top : ℤ) (N n : ℕ) (hn : n≤N)
    (f : ℝ → ℝ) (x : ℝ) :
    |cellMean q (top-(n:ℤ)) f x| ≤ dyadicMaximal q top N f x := by
  change |cellMean q (top-(n:ℤ)) f x| ≤
    (Finset.range (N+1)).sup' Finset.nonempty_range_add_one
      (fun i : ℕ => |cellMean q (top-(i:ℤ)) f x|)
  exact Finset.le_sup' (fun i : ℕ => |cellMean q (top-(i:ℤ)) f x|)
    (Finset.mem_range.mpr (show n<N+1 by omega))

theorem horizontalMaximal_nonneg (q top : ℤ) (N : ℕ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤horizontalMaximal q top N f z := dyadicMaximal_nonneg _ _ _ _ _

theorem verticalMaximal_nonneg (q top : ℤ) (N : ℕ) (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤verticalMaximal q top N f z := horizontalMaximal_nonneg _ _ _ _ _

theorem strongDyadicMaximal_nonneg (qx qy topx topy : ℤ) (Nx Ny : ℕ)
    (f : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    0≤strongDyadicMaximal qx qy topx topy Nx Ny f z := horizontalMaximal_nonneg _ _ _ _ _

/-- Monotonicity of a literal cell average; integrability is only needed
on the one cell in question. -/
theorem cellMean_mono (q k : ℤ) (x : ℝ) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (cell q k (index q k x)))
    (hg : IntegrableOn g (cell q k (index q k x)))
    (hfg : ∀ y∈cell q k (index q k x), f y≤g y) :
    cellMean q k f x≤cellMean q k g x := by
  unfold cellMean
  apply div_le_div_of_nonneg_right _ (scale_pos k).le
  exact setIntegral_mono_on hf hg (cell_measurable q k (index q k x)) hfg

end LipschitzHilbert.DyadicLineGrid

end

end OAI
