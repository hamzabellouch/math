import OAI.Analysis.LipschitzHilbert.Phase.SourceSupportedSelectorPathPredictor
import OAI.Analysis.LipschitzHilbert.Phase.SourcePathPrediction
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseSnapshot
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseDropComparison
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotChoice

namespace OAI

/-! Physical packet prediction patched on the literal marked cells of
the single reverse grid. Snapshots are chosen on each fixed physical line. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_reverse_path_predictor
    (pProfile q Cmass Cweight Cfreq c0 A_M : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι κ : Type) [Fintype κ]
      (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : ι → SourceLabeledLattice N κ Label Item),
      (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
      (∀ t ∈ tops, (P t).constant ≤ L^pProfile) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
      (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw Dweight) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
      (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(P t).length j) 0) →
    ∀ (hKb : 0 < SourceParameters.blockCount L), (SourceParameters.blockCount L:ℝ) ≤ L^2 →
    ∀ (σ : Fin (SourceParameters.blockCount L)) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (eta : κ → ℝ), (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
    ∀ (top : ι), top ∈ tops → ∀ (origin y : ℝ) (good : Set ℝ),
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
      0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
    let count := g.firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
    let beta := fun j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
      (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
      σ top (x,y+slope top*x) j
    let marked := fun j i => sourceMarkedCell
      (grid.cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
    (∀ x ∈ good, ∀ t ∈ tops, weight t (x,y+slope top*x) ≤ Cweight) →
    (∀ x ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t (x,y+slope top*x))) ≤ 3*L) →
    (∀ x ∈ good, (∑ t ∈ tops, weight t (x,y+slope top*x)) ≤ L^Cmass*Nmass) →
    (∀ x ∈ good, ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ z,
      |z-((y+slope top*x)-(T t).slope*x)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u x z‖+(T t).width*
        ‖covariantSignal (P t).frequency (fun k zz => (Q t).rawInterval (coeff t) 0 l u x zz k) z‖ ≤
          A*(weight t (x,y+slope top*x))^8) →
    (∀ j < count, ∀ x ∈ good, ∀ I : Finset ι, I ⊆ tops →
      (∀ t ∈ I, (T t).radius (x,y+slope top*x) ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ v ∈ I, t ≠ v →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |slope t-slope v|) →
      (I.card:ℝ) ≤ D/100) →
    ∀ j < count,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∀ x z, grid.index fine x = grid.index fine z → Γ x = Γ z) ∧
      (∀ i : Fin (grid.branching^grid.depth),
        (∫ x in {x | grid.index coarse x = i}, Γ x ∂volume.restrict grid.root) ≤
          (volume.restrict grid.root).real {x | grid.index coarse x = i}) ∧
      (∀ x ∈ grid.root, ¬marked j (grid.index coarse x).val → Γ x = 1) ∧
      ∀ x ∈ grid.root ∩ good, grid.markedValue coarse (marked j) (beta j) x ≤
        Real.exp (grid.markedError coarse (marked j)
          (fun x => (2*SourceParameters.step L^(-(1/32:ℝ)))*pathDrop (n x) j) x)*Γ x := by
  filter_upwards [eventually_source_supported_selector_path_predictor pProfile q Cmass Cweight Cfreq c0
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0,
    eventually_source_reverse_drop_comparison (Dweight:ℝ) (by positivity)] with L hpred hdrop
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN eta hetaLo hetaHi hPeta top htop origin y good
  dsimp only
  intro hweight htotal hmass hconc hcount
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let count := g.firstIneligibleShiftedBlock cut (precision top)
    (div_pos hw (T top).length_pos) hKb σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  let n := fun x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
    (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
    0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
  let beta := fun j x => g.sourceShiftedPathPrediction tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
    (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
    σ top (x,y+slope top*x) j
  let marked := fun j i => sourceMarkedCell
    (grid.cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
    (fun x => n x j) (fun x => n x j-n x (j+1)) (L^A_M)
  intro j hj
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  apply grid.exists_marked_prediction_from_snapshots coarse fine
    (ShiftedBlocks.reverseLevel_monotone hKb σ count (Nat.le_succ _))
    (ShiftedBlocks.reverseLevel_le σ count _) (marked j) good (beta j)
    (fun x => pathDrop (n x) j)
    (SourceParameters.step L^(-(1/32:ℝ)))
    (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  · intro i hi _hm x₀ hx₀
    let win := grid.lineWindow coarse i (fine-coarse)
    have hxwin : x₀ ∈ win.root := by
      change x₀ ∈ (grid.lineWindow coarse i (fine-coarse)).root
      rw [FiniteLineGrid.lineWindow_root]
      exact hx₀.1
    have hwin : win = sourceLineGrid L win.origin
        (sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)))
        (ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j)
        (sourceLineScale_pos g L hw (ShiftedBlocks.endpoint σ (j+1))) := by
      simpa only [FiniteLineGrid.atSnapshot,sub_zero] using
        source_reverse_snapshot_window g L origin hw σ hKb hj hbranch i 0
    have he := g.eligible_before_firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ hj
    have hwp (t : ι) (z : ℝ × ℝ) : 0 < weight t z :=
      (T t).weight_pos (zero_lt_one.trans_le hKw) _ z
    have hu : 0 ≤ pathDrop (n x₀) j := pathDrop_nonnegative (n x₀) j
      (g.shiftedPathMass_pos tops slope precision cut weight hwp σ top htop _ j he)
      (g.shiftedPathMass_antitone tops slope precision cut weight
        (fun t _ => (div_pos hw (T t).length_pos).le) (fun t z => (hwp t z).le)
        hKb σ top htop _ (Nat.le_succ j))
    have hmass₀ := (g.mass_le_total tops slope precision cut weight
      (fun t z => (hwp t z).le) (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) (x₀,y+slope top*x₀)).trans
      (hmass x₀ hx₀.2)
    obtain ⟨F,_hFm,hFi,hFp,hFa,hFc,hFb⟩ := hpred ι κ tops T N Label Item P hslots hP
      alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w hw hbranch hwidth
      hlength hzero hKb hKbL σ j M hM hMmax phase a Z A maskExponent D Nmass
      ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask hD hNmass hlogN
      (x₀,y+slope top*x₀) eta hetaLo hetaHi hPeta (hweight x₀ hx₀.2)
      (htotal x₀ hx₀.2) (hconc x₀ hx₀.2)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) (slope top) win.origin
      (pathDrop (n x₀) j) rfl top htop rfl he hu hmass₀ le_rfl
      hxwin.1 (by rw [← hwin]; exact hxwin.2.le) (hcount j hj x₀ hx₀.2)
    rw [← hwin] at hFi hFa hFc hFb
    have hlen := ShiftedBlocks.reverseLevel_block_length hKb σ hj
    refine ⟨F,hFp,hFi,hFa,?_,?_⟩
    · intro x z hxz
      change win.index (fine-coarse) x = win.index (fine-coarse) z at hxz
      exact hFc x z (by simpa only [show fine-coarse = _ from hlen] using hxz)
    · intro x hx
      have hxx : x ∈ win.root := by
        change x ∈ (grid.lineWindow coarse i (fine-coarse)).root
        rw [FiniteLineGrid.lineWindow_root]
        exact hx.1
      have hb := hFb x hxx
      have hpoint : y+slope top*x₀+slope top*(x-x₀) = y+slope top*x := by ring
      simpa only [beta,sourceShiftedPathPrediction,sourceBlockPrediction,hpoint] using hb
  · intro i _hi _hm x₀ hx₀ x hx
    exact (hdrop ι g tops T w Kw hw hKw hbranch hwidth hKb σ top htop origin y
      j hj i x hx.1 x₀ hx₀.1).1

end LipschitzHilbert.AngularGrid

end

end OAI
