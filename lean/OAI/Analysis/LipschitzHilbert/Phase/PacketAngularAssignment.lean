import OAI.Analysis.LipschitzHilbert.Phase.PacketAngularCover
import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeData
import OAI.Analysis.LipschitzHilbert.Trees.SourceThreeGridMaximal

namespace OAI

/-! A simultaneous choice of one of three angular grids for every
label. Its cells carry both the selector and the spectral margin. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem precision_eq_scaled_grid (w : ℝ) (j : Fin N) :
    w/P.length j = (w/P.topLength)*DyadicLineGrid.scale (j.val:ℤ) := by
  rw [length,DyadicLineGrid.scale,zpow_natCast]
  field_simp [P.topLength_pos.ne',pow_ne_zero _ (by norm_num : (2:ℝ)≠0)]

theorem exists_angular_assignment (w cStar cEta margin radius : ℝ)
    (hw : 0<w) (hcStar : 0≤cStar) (hcEta : 0<cEta) (hm : 0≤margin) (hr : 0≤radius)
    (hsmall : 6*max radius (cStar/cEta+margin)<1) :
    ∃ grid : ∀ j, P.labels j → DyadicLineGrid.GridChoice,
    ∃ cell : ∀ j, P.labels j → ℤ,
      ∀ j (l : P.labels j),
        (∀ s, |s-P.rowSlope j l|≤radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta|≤cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) (grid j l).val j.val (cell j l)) := by
  classical
  have h (j : Fin N) (l : P.labels j) :
      ∃ g : DyadicLineGrid.GridChoice, ∃ cell : ℤ,
        (∀ s, |s-P.rowSlope j l|≤radius*(w/P.length j) →
          s∈scaledAngularCell (w/P.topLength) g.val j.val cell) ∧
        (∀ xi eta, cEta≤w*eta →
          |xi+P.rowSlope j l*eta|≤cStar/P.length j →
          Icc (-xi/eta-margin*(w/P.length j)) (-xi/eta+margin*(w/P.length j)) ⊆
            scaledAngularCell (w/P.topLength) g.val j.val cell) := by
    obtain ⟨g,hg,cell,hsel,hspec⟩ := PacketRepresentation.exists_packet_angular_cell
      (w/P.topLength) (div_pos hw P.topLength_pos) j.val
      (P.length j) w (P.rowSlope j l) cEta cStar margin radius
      (P.length_pos j) hw hcEta hcStar hm hr (P.precision_eq_scaled_grid w j) hsmall
    refine ⟨⟨g,hg⟩,cell,hsel,?_⟩
    intro xi eta hV hX
    apply hspec xi eta hV
    rw [PacketRepresentation.symbolX,abs_mul,abs_of_pos (P.length_pos j)]
    have hh := (le_div_iff₀ (P.length_pos j)).mp hX
    simpa only [mul_comm] using hh
  choose grid cell hcell using h
  exact ⟨grid,cell,hcell⟩

end LipschitzHilbert.PacketLatticeData

namespace LipschitzHilbert.PacketRepresentation

theorem angular_cell_subset_unit (unit : ℝ) (hu : 0<unit) (grid level cell : ℤ)
    (theta : ℝ) (htheta : theta∈scaledAngularCell unit grid level cell)
    (hsmall : |theta|+unit*DyadicLineGrid.scale level≤1) :
    scaledAngularCell unit grid level cell ⊆ Icc (-1) 1 := by
  intro s hs
  have hd := scaledAngularCell_slope hu (le_refl level) ⟨theta,htheta,htheta⟩ hs htheta
  have hb : |s|≤1 := calc
    _ = |(s-theta)+theta| := by congr 1; ring
    _ ≤ |s-theta|+|theta| := abs_add_le _ _
    _ ≤ 1 := by linarith
  exact abs_le.mp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
