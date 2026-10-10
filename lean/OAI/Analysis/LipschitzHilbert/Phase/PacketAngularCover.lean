import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityScaledForest
import OAI.Analysis.LipschitzHilbert.Geometry.SourceThreeGridCover
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBandSymbol

namespace OAI

/-! Fixed-scale angular cells containing both the packet spectrum and
its selector support. The three nested grids are the existing literal
alternating one-third grids. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

theorem exists_scaled_three_grid_cover (unit : ℝ) (hu : 0<unit)
    (k : ℤ) (c r : ℝ) (hr : 0≤r)
    (hsmall : 6*r<unit*DyadicLineGrid.scale k) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      Icc (c-r) (c+r) ⊆ scaledAngularCell unit grid k cell := by
  have hs : 6*(r/unit)<DyadicLineGrid.scale k := by
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hu).2
    simpa only [mul_comm] using hsmall
  obtain ⟨grid,hg,cell,hc⟩ := DyadicLineGrid.exists_three_grid_cover k
    (c/unit) (r/unit) (div_nonneg hr hu.le) hs
  refine ⟨grid,hg,cell,?_⟩
  intro x hx
  apply hc
  constructor
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.1
    convert h using 1
    ring
  · have h := (div_le_div_iff_of_pos_right hu).mpr hx.2
    convert h using 1
    ring

theorem frequency_margin_subset {S : Set ℝ} (l w xi eta theta c C margin : ℝ)
    (hl : 0<l) (hw : 0<w) (hc : 0<c) (hC : 0≤C) (_hm : 0≤margin)
    (hV : c≤w*eta) (hX : |symbolX l xi eta theta|≤C)
    (hcell : Icc (theta-(C/c+margin)*(w/l))
      (theta+(C/c+margin)*(w/l)) ⊆ S) :
    Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆ S := by
  have hs := abs_le.mp (frequency_slope_margin l w xi eta theta c C hl hw hc hC hV hX)
  intro s hs'
  apply hcell
  constructor <;> nlinarith only [hs.1,hs.2,hs'.1,hs'.2]

/-- A single selected angular cell contains the selector support and the
entire spectrum with the requested margin. -/
theorem exists_packet_angular_cell (unit : ℝ) (hu : 0<unit) (k : ℤ)
    (l w theta c C margin radius : ℝ) (hl : 0<l) (hw : 0<w)
    (hc : 0<c) (hC : 0≤C) (hm : 0≤margin) (hr : 0≤radius)
    (hprecision : w/l=unit*DyadicLineGrid.scale k)
    (hsmall : 6*max radius (C/c+margin)<1) :
    ∃ grid∈Finset.Icc (-1) 1, ∃ cell : ℤ,
      (∀ s, |s-theta|≤radius*(w/l) → s∈scaledAngularCell unit grid k cell) ∧
      (∀ xi eta, c≤w*eta → |symbolX l xi eta theta|≤C →
        Icc (-xi/eta-margin*(w/l)) (-xi/eta+margin*(w/l)) ⊆
          scaledAngularCell unit grid k cell) := by
  have hd : 0<w/l := div_pos hw hl
  let R := max radius (C/c+margin)
  have hR : 0≤R := hr.trans (le_max_left _ _)
  obtain ⟨grid,hg,cell,hcell⟩ := exists_scaled_three_grid_cover unit hu k theta
    (R*(w/l)) (mul_nonneg hR hd.le) (by
      rw [←hprecision]
      have h := mul_lt_mul_of_pos_right hsmall hd
      convert h using 1 <;> ring)
  refine ⟨grid,hg,cell,?_,?_⟩
  · intro s hs
    apply hcell
    have hs' := abs_le.mp hs
    have hle := mul_le_mul_of_nonneg_right (le_max_left radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith
  · intro xi eta hV hX
    apply frequency_margin_subset l w xi eta theta c C margin hl hw hc hC hm hV hX
    intro s hs
    apply hcell
    have hle := mul_le_mul_of_nonneg_right (le_max_right radius (C/c+margin)) hd.le
    constructor <;> dsimp only [R] at * <;> linarith only [hs.1,hs.2,hle]

end LipschitzHilbert.PacketRepresentation

end

end OAI
