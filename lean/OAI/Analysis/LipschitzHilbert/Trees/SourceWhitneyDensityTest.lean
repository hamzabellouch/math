import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCellDensity

namespace OAI

/-! The actual parent witness furnishes an admissible density test at a
length between sixteen and thirty-two Whitney lengths. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

theorem center_mem_cell (k j : ℤ) : center k j∈cell 0 k j := by
  have hs := scale_pos k
  have hr : left 0 k (j+1)=left 0 k j+scale k := by
    simp only [left,Int.cast_add,Int.cast_one]
    ring
  change left 0 k j≤center k j ∧ center k j<left 0 k (j+1)
  rw [hr]
  unfold center
  constructor <;> linarith only [hs]

/-- No compatibility of the horizontal grid origin with the packet
length is assumed: the test length is selected in the source scale grid. -/
theorem exists_comparable_test_length (ell0 r : ℝ) (hell0 : 0<ell0) (hr : 0<r) :
    ∃ level : ℤ, 16*r≤ell0/scale level ∧ ell0/scale level<32*r := by
  obtain ⟨level,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0<ell0/(16*r) by positivity) (by norm_num : (1:ℝ)<2)
  change scale level≤ell0/(16*r) at hlo
  change ell0/(16*r)<scale (level+1) at hhi
  have hlo' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<16) hr)).mp hlo
  have hhi' := (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<16) hr)).mp hhi
  rw [scale_succ] at hhi'
  refine ⟨level,(le_div_iff₀ (scale_pos level)).mpr ?_,(div_lt_iff₀ (scale_pos level)).mpr ?_⟩
  · nlinarith only [hlo']
  · nlinarith only [hhi']

/-- A Whitney interval admitting a tile longer than thirty-two interval
lengths has an actual density test containing its parent witness. -/
theorem exists_whitney_density_test {ι : Type*} (tiles : Finset ι)
    (tile : ι → OrdinaryDensityTile) (ell0 w W tau slope y : ℝ) (grid k j : ℤ)
    (hell0 : 0<ell0) (hW : 0<W)
    (hWhitney : Whitney tiles (fun i => (tile i).center.1)
      (fun i => ell0/scale (tile i).level) k j)
    (hshort : ∀ i∈tiles, ell0/scale (tile i).level≤tau)
    (hcenter : ∀ i∈tiles, |(tile i).center.2-y-slope*(tile i).center.1|≤W/2)
    (hslope : ∀ i∈tiles, slope∈scaledAngularCell (w/ell0) grid (tile i).level (tile i).cell)
    (hlong : ∃ i∈tiles, 32*scale k<ell0/scale (tile i).level) :
    ∃ i∈tiles, ∃ test : OrdinaryDensityTest ell0 w W tau grid (tile i),
      test.top.x=center k j ∧ test.top.y=y+slope*center k j ∧
      test.top.slope=slope ∧ 16*scale k≤test.top.length ∧ test.top.length<32*scale k := by
  obtain ⟨i,hi,hlen,hnear⟩ := parent_witness tiles _ _ hWhitney
  obtain ⟨level,hlo,hhi⟩ := exists_comparable_test_length ell0 (scale k) hell0 (scale_pos k)
  let len := ell0/scale level
  change 16*scale k≤len at hlo
  change len<32*scale k at hhi
  have hlen0 : 0<len := div_pos hell0 (scale_pos level)
  have htau : len≤tau := by
    obtain ⟨s,hs,hslen⟩ := hlong
    exact hhi.le.trans (hslen.le.trans (hshort s hs))
  let T : SlopeBox := ⟨center k j,y+slope*center k j,slope,len,W,hlen0,hW⟩
  have hcenter_mem : (tile i).center∈densitySpatialBox T (1/2) := by
    have hx := hnear (center k j) (center_mem_cell k j)
    have hy := hcenter i hi
    change |(tile i).center.1-center k j|≤(1/2)*len ∧
      |((tile i).center.2-(y+slope*center k j))-slope*((tile i).center.1-center k j)|≤(1/2)*W
    constructor
    · linarith only [hx,hlo,scale_pos k]
    · have he : ((tile i).center.2-(y+slope*center k j))-slope*((tile i).center.1-center k j)=
          (tile i).center.2-y-slope*(tile i).center.1 := by ring
      rw [he]
      linarith only [hy]
  let test : OrdinaryDensityTest ell0 w W tau grid (tile i) := {
    top := T
    level := level
    cell := index grid level (slope/(w/ell0))
    length_eq := rfl
    width_eq := rfl
    length_le := htau
    tile_length_le := by change ell0/scale (tile i).level≤len; linarith only [hlen,hlo,scale_pos k]
    center_mem := hcenter_mem
    slope_mem_tile := hslope i hi
    slope_mem_self := mem_index_cell grid level (slope/(w/ell0)) }
  exact ⟨i,hi,test,rfl,rfl,rfl,hlo,hhi⟩

/-- The test selected from the parent witness gives the manuscript's
polynomial cell-density bound, simultaneously at every transverse index. -/
theorem exists_whitney_cell_density {ι : Type*} (tiles : Finset ι)
    (tile : ι → OrdinaryDensityTile) (ell0 w W tau slope y : ℝ) (grid k j : ℤ)
    (hell0 : 0<ell0) (hW : 0<W)
    (hWhitney : Whitney tiles (fun i => (tile i).center.1)
      (fun i => ell0/scale (tile i).level) k j)
    (hshort : ∀ i∈tiles, ell0/scale (tile i).level≤tau)
    (hcenter : ∀ i∈tiles, |(tile i).center.2-y-slope*(tile i).center.1|≤W/2)
    (hslope : ∀ i∈tiles, slope∈scaledAngularCell (w/ell0) grid (tile i).level (tile i).cell)
    (hlong : ∃ i∈tiles, 32*scale k<ell0/scale (tile i).level)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ i∈tiles, (tile i).density ell0 w W tau grid E u≤eta) :
    ∃ i∈tiles, ∃ test : OrdinaryDensityTest ell0 w W tau grid (tile i),
      test.top.x=center k j ∧ test.top.y=y+slope*center k j ∧
      test.top.slope=slope ∧ 16*scale k≤test.top.length ∧ test.top.length<32*scale k ∧
      ∀ n : ℤ,
        let A := E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell∩treeCell slope y W k j n
        IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) ∧
        (volume.prod volume).real A≤32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*scale k*W := by
  obtain ⟨i,hi,test,hx,hy,ht,hlo,hhi⟩ := exists_whitney_density_test tiles tile ell0 w W tau slope y
    grid k j hell0 hW hWhitney hshort hcenter hslope hlong
  refine ⟨i,hi,test,hx,hy,ht,hlo,hhi,?_⟩
  intro n
  have hR : 0≤1+|(n:ℝ)| := by positivity
  have hrad : ∀ z∈treeCell slope y W k j n, test.top.radius z≤1+|(n:ℝ)| := by
    intro z hz
    apply treeCell_radius_bound test.top slope y k j n hx
      (by simpa only [hx] using hy) ht (by linarith only [hlo,scale_pos k])
    simpa only [test.width_eq] using hz
  have hm := density_test_cell_mass ell0 w W tau grid (tile i) test E hE u hu
    (treeCell slope y W k j n) (treeCell_measurable slope y W k j n)
    (1+|(n:ℝ)|) eta hR hrad (hdensity i hi)
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hpow : (1+(1+|(n:ℝ)|))^203≤(2:ℝ)^203*(1+|(n:ℝ)|)^203 := by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith only [abs_nonneg (n:ℝ)]
  have hpow0 : 0≤(2:ℝ)^203*(1+|(n:ℝ)|)^203 := by positivity
  calc
    (1+(1+|(n:ℝ)|))^203*eta*test.top.area ≤
        ((2:ℝ)^203*(1+|(n:ℝ)|)^203)*eta*test.top.area :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow heta) test.top.area_pos.le
    _ ≤ ((2:ℝ)^203*(1+|(n:ℝ)|)^203)*eta*((32*scale k)*W) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hpow0 heta)
      rw [SlopeBox.area,test.width_eq]
      exact mul_le_mul_of_nonneg_right hhi.le hW.le
    _ = _ := by ring

end LipschitzHilbert.SourceWhitney

end

end OAI
