import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeData
import OAI.Analysis.LipschitzHilbert.Packets.SourceDensityPacketGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeDensityTerm
import OAI.Analysis.LipschitzHilbert.Geometry.SourceShortTreeOverlap

namespace OAI

/-! Own-box density and the short-packet estimate for unrestricted
lattice slopes. Only the intrinsic two-dimensional profile is used. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

abbrev PacketIndex := Σ j : Fin N, Σ l : P.labels j, Item j l

def densityTile (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ)
    (q : P.PacketIndex) : OrdinaryDensityTile where
  center := (P.actualX q.1 q.2.1 q.2.2,
    P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2)
  level := q.1.val
  cell := cell q.1 q.2.1

def ordinaryDensity (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (q : P.PacketIndex) : ℝ :=
  (P.densityTile oldSlope cell q).density P.topLength w P.width tau grid E u

/-- The actual spatial rectangle and direction of a source packet. -/
def ownBox (oldSlope : ℝ) (q : P.PacketIndex) : SlopeBox where
  x := P.actualX q.1 q.2.1 q.2.2
  y := P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2
  slope := oldSlope+P.rowSlope q.1 q.2.1
  length := P.length q.1
  width := P.width
  length_pos := P.length_pos q.1
  width_pos := P.width_pos

/-- The ordinary density includes each packet's own rectangle. -/
def ownDensityTest (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ)
    (grid : ℤ) (w tau : ℝ) (q : P.PacketIndex)
    (hlen : P.length q.1≤tau)
    (hslope : oldSlope+P.rowSlope q.1 q.2.1 ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    OrdinaryDensityTest P.topLength w P.width tau grid (P.densityTile oldSlope cell q) where
  top := P.ownBox oldSlope q
  level := q.1.val
  cell := cell q.1 q.2.1
  length_eq := by simp only [ownBox,length,DyadicLineGrid.scale,zpow_natCast]
  width_eq := rfl
  length_le := hlen
  tile_length_le := by
    simpa only [densityTile,ownBox,length,DyadicLineGrid.scale,zpow_natCast] using le_refl (P.length q.1)
  center_mem := by
    simp only [densitySpatialBox,densityTile,ownBox,mem_ofPred_eq,sub_self,mul_zero,abs_zero]
    exact ⟨mul_nonneg (by norm_num) (P.length_pos q.1).le,
      mul_nonneg (by norm_num) P.width_pos.le⟩
  slope_mem_tile := hslope
  slope_mem_self := hslope

/-- A literal source packet restricted to a Whitney strip. Its decay
factor is precisely the one summed in `SourceShortTreeSum`. -/
theorem own_packet_whitney_density_bound
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (q : P.PacketIndex) (hlen : P.length q.1≤tau)
    (hslope : oldSlope+P.rowSlope q.1 q.2.1 ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (horder : 205≤2*P.order) (M sigma eta : ℝ) (hM : 0≤M) (hsigma : 0≤sigma)
    (coefficient : EuclideanSpace ℂ κ) (hcoefficient : ‖coefficient‖≤sigma)
    (selector : κ → ℝ → ℂ) (hselector : ∀ a, Measurable (selector a))
    (hbound : ∀ a s, ‖selector a s‖≤M)
    (hsupport : ∀ a s, selector a s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (hdensity : P.ordinaryDensity oldSlope cell grid w tau E u q≤eta) (k j : ℤ) :
    let F := fun z : ℝ×ℝ => WithLp.toLp 2 (fun a => coefficient a*selector a (u z)*
      P.physicalPacket oldSlope q.1 q.2.1 q.2.2 a z)
    IntegrableOn (fun z => ‖F z‖) (E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 k j) (volume.prod volume) ∧
    (∫ z in E∩Prod.fst ⁻¹' DyadicLineGrid.cell 0 k j, ‖F z‖ ∂volume.prod volume) ≤
      (3:ℝ)^203*P.profileBound*M*sigma*eta*(P.length q.1)*P.width*
        (1+(SourceWhitney.stripDistance (SourceWhitney.center k j) (DyadicLineGrid.scale k)
          (P.actualX q.1 q.2.1 q.2.2)/(P.length q.1))^2)⁻¹^2 := by
  let test := P.ownDensityTest oldSlope cell grid w tau q hlen hslope
  have h := density_test_short_packet_term P.topLength w P.width tau grid
    (P.densityTile oldSlope cell q) test 2 (2*P.order) horder
    P.profileBound M sigma eta
    (SourceWhitney.stripDistance (SourceWhitney.center k j) (DyadicLineGrid.scale k)
      (P.actualX q.1 q.2.1 q.2.2))
    P.profileBound_pos.le hM hsigma (SourceWhitney.stripDistance_nonneg _ _ _)
    (P.profile q.1 q.2.1 q.2.2) P.frequency (P.profile_bound q.1 q.2.1 q.2.2)
    coefficient hcoefficient selector hselector hbound hsupport u hu E hE
    (DyadicLineGrid.cell 0 k j) (DyadicLineGrid.cell_measurable 0 k j)
    (fun x hx => SourceWhitney.stripDistance_le_point (P.actualX q.1 q.2.1 q.2.2) k j hx)
    hdensity
  refine ⟨h.1,?_⟩
  exact h.2.trans_eq (by simp only [test,ownDensityTest,ownBox,SlopeBox.area]; ring)


end LipschitzHilbert.PacketLatticeData

end

end OAI
