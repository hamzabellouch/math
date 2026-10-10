import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkedFactorsIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseCellMarking

namespace OAI

/-! Integration on the actual first-terminal reverse grid. Literal cell
marking and the actual path mass discharge every stopping-budget premise. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_reverse_marked_integral (D C A_M : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length) 0 →
    ∀ (origin y Nmass : ℝ), 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (good : Set ℝ), MeasurableSet good →
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let level := ShiftedBlocks.reverseLevel σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    let marked := fun j i => sourceMarkedCell
      (grid.cell (level (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ beta : ℕ → ℝ → ℝ, (∀ j, Measurable (beta j)) →
      (∀ x ∈ grid.root ∩ good, ∀ j < count, 0 ≤ beta j x) →
    (∀ j < count, ∃ Γ : ℝ → ℝ, (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, grid.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        grid.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ x = Γ z) ∧
      (∀ i : Fin (grid.branching^grid.depth),
        (∫ x in {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
          Γ x ∂volume.restrict grid.root) ≤
          (volume.restrict grid.root).real {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i}) ∧
      ∀ x ∈ grid.root ∩ good, reverseMarkedValue grid level count marked beta j x ≤
        Real.exp (reverseMarkedError grid level count marked
          (fun j x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) j x)*Γ x) →
    (∀ x ∈ good, (∑ t ∈ tops, (T t).weight Kw D (x,y+(T top).slope*x)) ≤ L^C*Nmass^2) →
    IntegrableOn (good.indicator (fun x => (T top).weight Kw D (x,y+(T top).slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid level count marked beta j x)) grid.root volume ∧
    (∫ x in grid.root, good.indicator (fun x => (T top).weight Kw D (x,y+(T top).slope*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid level count marked beta j x) x) ≤
      Real.exp 1*Real.exp (2*D)*∫ x in grid.root, (T top).weight Kw D (x,y+(T top).slope*x) := by
  filter_upwards [eventually_source_reverse_cell_marking D A_M hD hAM,
    eventually_source_marked_drop_budget C A_M hC hAM,eventually_ge_atTop (1:ℝ)]
    with L hmark hbudget hL
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top htop hzero
    origin y Nmass hN hlog good hgood
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  let level := ShiftedBlocks.reverseLevel σ count
  let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
    σ top (x,y+(T top).slope*x)
  let marked := fun j i => sourceMarkedCell
    (grid.cell (level (ShiftedBlocks.reverseIndex count j)) i)
    (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
  intro beta hbeta hnonneg hpredict hmass
  have hfactor : ∀ j : ℕ, ∃ Γ : ℝ → ℝ, j < count →
      (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, grid.index (level (ShiftedBlocks.reverseIndex count j+1)) x =
        grid.index (level (ShiftedBlocks.reverseIndex count j+1)) z → Γ x = Γ z) ∧
      (∀ i : Fin (grid.branching^grid.depth),
        (∫ x in {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i},
          Γ x ∂volume.restrict grid.root) ≤
          (volume.restrict grid.root).real {x | grid.index (level (ShiftedBlocks.reverseIndex count j)) x = i}) ∧
      ∀ x ∈ grid.root ∩ good, reverseMarkedValue grid level count marked beta j x ≤
        Real.exp (reverseMarkedError grid level count marked
          (fun j x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) j x)*Γ x := by
    intro j
    by_cases hj : j < count
    · obtain ⟨Γ,hΓ⟩ := hpredict j hj
      exact ⟨Γ,fun _ => hΓ⟩
    · exact ⟨fun _ => 1,fun h => (hj h).elim⟩
  choose Γ hΓ using hfactor
  have hwp (t : ι) (z : ℝ × ℝ) : 0 ≤ (T t).weight Kw D z :=
    ((T t).weight_pos (zero_lt_one.trans_le hKw) D z).le
  have hlevels := sourceReverseLineGrid_levels g L origin hw σ hK count
  apply source_marked_factors_integral grid (T top) Kw D y 1 hKw hD
    (g.source_first_terminal_grid_width L origin hbranch hK σ hw (T top).length_pos hzero)
    level count hlevels.1 hlevels.2 good marked beta
    (fun j x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) Γ
    (fun j hj => (hΓ j hj).1) (fun j hj => (hΓ j hj).2.1)
    (fun j hj => (hΓ j hj).2.2.1) hnonneg
    (fun x hx j hj => (hΓ j hj).2.2.2 x hx)
  · intro x hx
    apply hbudget (n x) count
      (fun j => marked j (grid.index (level (ShiftedBlocks.reverseIndex count j)) x).val)
      Nmass hN hlog
    · exact (g.shiftedPathMass_le_total tops _ _ cut _ hwp σ top _ 0).trans (hmass x hx.2)
    · exact g.shiftedPathMass_nonneg tops _ _ cut _ hwp σ top _
    · exact g.shiftedPathMass_antitone tops _ _ cut _
        (fun t _ => (div_pos hw (T t).length_pos).le) hwp hK σ top htop _
    · have hz := g.shiftedPathMass_terminal_zero tops (fun t => (T t).slope)
        (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z) σ top count
        (g.firstIneligibleShiftedBlock_spec cut (w/(T top).length)
          (div_pos hw (T top).length_pos) hK σ) (x,y+(T top).slope*x)
      exact hz.trans_le (Real.rpow_nonneg (by linarith : 0 ≤ L) _)
    · intro j hj hm
      let coarse := level (ShiftedBlocks.reverseIndex count j)
      have hc : coarse ≤ grid.depth := ShiftedBlocks.reverseLevel_le σ count _
      have hxcell : x ∈ grid.cell coarse (grid.index coarse x).val :=
        (grid.index_eq_iff_mem_cell hc hx.1 _).mp rfl
      exact (hmark ι g tops T w Kw hw hKw hbranch hwidth hK σ top origin y
        j hj (grid.index coarse x).val x hxcell).1 hm |>.1
  · apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ hgood
    apply Measurable.mul
    · exact ((T top).continuous_weight (zero_lt_one.trans_le hKw) D).measurable.comp (by fun_prop)
    · apply Finset.measurable_prod
      intro j _
      exact grid.measurable_markedValue _ _ _ (hbeta j)

end LipschitzHilbert.AngularGrid

end

end OAI
