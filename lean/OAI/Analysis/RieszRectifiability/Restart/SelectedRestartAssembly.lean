import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.OriginalADRestartCoverage
import OAI.Analysis.RieszRectifiability.Restart.GoodRegionRestartAssembly

namespace OAI

/-!
# Surface data for selected restart assembly

Finite Lipschitz surface pieces and an active-region limit model supply the parent chart
at a good restart. At a bad restart the selected stop is the root, so immediate-child
assembly suffices. Both cases share a bound given by two restart-chart steps.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

/-- Plane fits, a limit model, and bounded surface pieces covering the restart set. -/
structure SelectedRestartSurfaceData (n : ℕ)
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (ε : ℝ) (N : ℕ) (P : ℝ≥0) where
  planes : SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ →
    AffineSubspace ℝ (Ambient d)
  isPlane : ∀ i, IsAffineNPlane n (planes i)
  fits : ∀ i, activeRegionCell (relativeRestartGood Bad q) i →
    bilateralPlaneError μ i.center (1024 * i.radius) (planes i) < ε
  model : planes (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) → Ambient d
  isModel : IsActiveRegionLimitModel μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
    (relativeRestartGood Bad q) planes isPlane ε model
  domains : Fin N → Set (Ambient n)
  domains_bounded : ∀ j, domains j ⊆ ball (0 : Ambient n) q.radius
  pieces : Fin N → Ambient n → Ambient d
  pieces_lipschitz : ∀ j, LipschitzOnWith P (pieces j) (domains j)
  pieces_bounded : ∀ j, pieces j '' domains j ⊆ closedBall q.center (3 * q.radius)
  pieces_cover : E = ⋃ j : Fin N, pieces j '' domains j

/-- Embed an immediate child of a relative selected stop into the next restart nodes. -/
def selectedRestartChildNode (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (i : relativeSelectedRestartStops Bad q E)
    (j : supportImmediateChildren μ R hR (k + q.depth + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩) : selectedRestartNext Bad q E :=
  ⟨⟨q.compose (i.val.compose j.val), selected_restart_child_is_restart Bad q E i j⟩,
    ⟨i, j, rfl⟩⟩

theorem exists_chart_at_equal_radius (r s : ℝ) (hrs : r = s)
    (f : ball (0 : Ambient n) r → Ambient d) (M : ℝ≥0) (hf : LipschitzWith M f) :
    ∃ g : ball (0 : Ambient n) s → Ambient d,
      LipschitzWith M g ∧ Set.range g = Set.range f := by
  subst s
  exact ⟨f, hf, rfl⟩

theorem relative_selected_stop_eq_root_of_bad
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (hq : Bad q) (E : Set (Ambient d))
    (i : relativeSelectedRestartStops Bad q E) :
    i.val = supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ := by
  apply i.val.eq_root_of_zero_depth
  by_contra hi
  have hgood := i.property.1.2
    (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)
    (Nat.pos_of_ne_zero hi) i.val.cell_subset_top
  change ¬ Bad (q.compose (supportCellRoot μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩)) at hgood
  exact hgood (q.compose_root ▸ hq)

/-- Assemble child charts and the parent surface with a uniform two-step Lipschitz bound. -/
theorem has_selected_restart_assembly_of_surface_data (hn : 0 < n)
    (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
    (ε : ℝ) (hε : 0 < ε) (hεfine : ε ≤ 1 / 281474976710656)
    (hsmall : activeProjectionError d ε ≤ 1 / 128) (N : ℕ) (P : ℝ≥0)
    (data : ∀ q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q},
      ¬ Bad q.val → SelectedRestartSurfaceData n Bad q.val (E q) ε N P) :
    HasSelectedRestartAssembly n Bad E
      (fun M => restartChartStepConstant d N P (restartChartStepConstant d N P M)) := by
  classical
  intro q M child hchildLip hchildImage
  have hlocal (i : relativeSelectedRestartStops Bad q.val (E q))
      (j : supportImmediateChildren μ R hR (k + q.val.depth + i.val.depth)
        ⟨i.val.center, i.val.mem_net⟩) :
      ∃ f : ball (0 : Ambient n) j.val.radius → Ambient d,
        LipschitzWith M f ∧ Set.range f = Set.range (child (selectedRestartChildNode Bad q.val (E q) i j)) := by
    apply exists_chart_at_equal_radius _ _ _ _ M
      (hchildLip (selectedRestartChildNode Bad q.val (E q) i j))
    change (q.val.compose (i.val.compose j.val)).radius = j.val.radius
    simp only [SupportCellDescendant.compose_radius]
  choose localChart hlocalLip hlocalRange using hlocal
  have hlocalImage (i : relativeSelectedRestartStops Bad q.val (E q))
      (j : supportImmediateChildren μ R hR (k + q.val.depth + i.val.depth)
        ⟨i.val.center, i.val.mem_net⟩) :
      Set.range (localChart i j) ⊆ closedBall j.val.center (2 * j.val.radius) := by
    rw [hlocalRange i j]
    have h := hchildImage (selectedRestartChildNode Bad q.val (E q) i j)
    change Set.range _ ⊆ closedBall j.val.center (2 * (q.val.compose (i.val.compose j.val)).radius) at h
    simpa only [SupportCellDescendant.compose_radius] using! h
  have hassembled : ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (restartChartStepConstant d N P (restartChartStepConstant d N P M)) g ∧
      Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      selectedRestartParent Bad q.val (E q) ⊆ Set.range g ∧
      ∀ i j, j.val.cell ∩ Set.range (localChart i j) ⊆ Set.range g := by
    by_cases hbad : Bad q.val
    · let root := supportCellRoot μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
      have hroot : root ∈ relativeSelectedRestartStops Bad q.val (E q) := by
        refine ⟨⟨?_, ?_⟩, Or.inl rfl⟩
        · change ¬ ¬ Bad (q.val.compose root)
          rw [SupportCellDescendant.compose_root]
          exact not_not.mpr hbad
        · intro i hi _
          exact False.elim (Nat.not_lt_zero i.depth hi)
      let i0 : relativeSelectedRestartStops Bad q.val (E q) := ⟨root, hroot⟩
      obtain ⟨g, hgLip, hgRange, hgCover, _⟩ := exists_immediate_child_chart_assembly hn
        μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
        (localChart i0) M (hlocalLip i0) (hlocalImage i0)
      have hconstant := (restartChartStepConstant_bounds d N P M).2.2.1.trans
        (restartChartStepConstant_bounds d N P (restartChartStepConstant d N P M)).1
      refine ⟨g, hgLip.weaken hconstant, hgRange, ?_, ?_⟩
      · intro x hx
        have hr := hx.1.2 root hx.1.1
        change ¬ Bad (q.val.compose root) at hr
        rw [SupportCellDescendant.compose_root] at hr
        exact False.elim (hr hbad)
      · intro i
        have hi : i = i0 := Subtype.ext (relative_selected_stop_eq_root_of_bad Bad q.val hbad (E q) i)
        subst i
        exact hgCover
    · let a := data q hbad
      let root := supportCellRoot μ R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
      have heq := selected_restart_stops_of_good_root Bad q.val hbad (E q)
      let lift := fun i : activeCellSelectedStopSet μ R hR (k + q.val.depth)
        ⟨q.val.center, q.val.mem_net⟩ (relativeRestartGood Bad q.val) root (E q) =>
          (⟨i.val, heq.symm ▸ i.property⟩ : relativeSelectedRestartStops Bad q.val (E q))
      obtain ⟨g, hgLip, hgRange, hgParent, hgCover, _⟩ := exists_good_region_restart_chart hn
        μ G hG hg R hR (k + q.val.depth) ⟨q.val.center, q.val.mem_net⟩
        (relativeRestartGood Bad q.val) a.planes a.isPlane ε hε hεfine hsmall a.fits
        a.model a.isModel root (relative_restart_root_active Bad q.val hbad)
        N a.domains a.domains_bounded a.pieces P a.pieces_lipschitz a.pieces_bounded (E q) a.pieces_cover
        (fun i => localChart (lift i)) M (fun i => hlocalLip (lift i)) (fun i => hlocalImage (lift i))
      refine ⟨g, hgLip.weaken (goodRegionRestartAssemblyConstant_le_two_steps d N P M), hgRange, ?_, ?_⟩
      · rw [selected_restart_parent_eq]
        exact hgParent
      · intro i j
        exact hgCover ⟨i.val, heq ▸ i.property⟩ j
  obtain ⟨g, hgLip, hgRange, hgParent, hgCover⟩ := hassembled
  refine ⟨g, hgLip, hgRange, hgParent, ?_⟩
  intro w x hx
  obtain ⟨i, j, hw⟩ := w.property
  have heq : selectedRestartChildNode Bad q.val (E q) i j = w :=
    Subtype.ext (Subtype.ext hw.symm)
  have hxcell : x ∈ j.val.cell := by
    have h := hx.1
    rw [hw, SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell] at h
    exact h
  have hxrange : x ∈ Set.range (localChart i j) := by
    rw [hlocalRange i j, heq]
    exact hx.2
  exact hgCover i j ⟨hxcell, hxrange⟩

end

end RieszRectifiability

end OAI
