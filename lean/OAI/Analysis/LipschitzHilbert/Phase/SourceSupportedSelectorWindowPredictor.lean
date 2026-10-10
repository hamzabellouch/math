import OAI.Analysis.LipschitzHilbert.Phase.SourceSupportedSelectorBlockPredictor
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseSnapshot

namespace OAI

/-! The physical source predictor transported from its chosen snapshot
to an arbitrary line window containing that snapshot. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_window_predictor
    (pProfile q Cmass Cweight Cfreq c0 : ℝ) (Dweight Bslots : ℕ)
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
    ∀ (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) (M : ι → ℕ),
      (∀ t ∈ tops, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ k, g.eligible (g.rootWidth/(SourceParameters.branching L)^2)
        (w/(T t).length) k → k ≤ M t) →
    ∀ (phase : Fin (SourceParameters.blockCount L) → ℂ) (a Z A maskExponent D Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (∀ τ, ‖phase τ‖ ≤ Z) →
      (∀ τ, τ ≠ σ → (phase τ).re = 0) →
      (phase σ).re = phaseMu D (Real.sqrt L) →
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 2 ≤ D → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ × ℝ) (eta : κ → ℝ),
      (∀ k, c0/w ≤ |eta k|) → (∀ k, |eta k| ≤ Cfreq/w) →
      (∀ t ∈ tops, (P t).frequency = eta) →
      (∀ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z ≤ Cweight) →
      Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (Dweight:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let lower := ShiftedBlocks.endpoint σ j
    let upper := ShiftedBlocks.endpoint σ (j+1)
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let slope := fun t => (T t).slope
    let precision := fun t => w/(T t).length
    let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
    let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
    let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => (Q p.1).rawBand
        (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
        0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
      (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤ A*(weight t z)^8) →
    ∀ (parent : ℤ) (sR origin u : ℝ), g.index lower sR = parent →
    let cells := g.sourceBlockCells tops slope precision cut lower upper parent
    let n := fun zz => g.mass tops slope precision cut weight lower parent zz
    let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
    let lam := fun zz (i : cells) => g.packetPathProduct
      (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
      lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
    let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
      (sourceLineScale_pos g L hw upper)
    ∀ i₀ : cells, 0 ≤ u → n z ≤ L^Cmass*Nmass →
      1-c z i₀/n z ≤ u →
      origin ≤ z.1 → z.1 ≤ origin+grid.width →
      (∀ I : Finset ι, I ⊆ tops → (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
        (∀ t ∈ I, precision t ≤ g.sourceGap L upper/(SourceParameters.branching L)^2) →
        (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*g.sourceGap L upper) →
        (∀ t ∈ I, ∀ v ∈ I, t ≠ v → g.sourceGap L upper ≤ |slope t-slope v|) →
        (I.card:ℝ) ≤ D/100) →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ b, 0 ≤ Γ b) ∧
        (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ b d, grid.index (upper-lower) b = grid.index (upper-lower) d → Γ b = Γ d) ∧
        ∀ b ∈ grid.root,
          sourcePredictionValue (Real.sqrt L) (phaseMu D (Real.sqrt L))
            (n ((b,z.2+sR*(b-z.1)))) (c ((b,z.2+sR*(b-z.1))))
            (fun i => wave ((b,z.2+sR*(b-z.1))) i.val) (lam ((b,z.2+sR*(b-z.1)))) ≤
            Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  filter_upwards [eventually_source_supported_selector_block_predictor pProfile q Cmass Cweight Cfreq c0
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0] with L hpred
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ j M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN z eta hetaLo hetaHi hPeta hweight htotal
  dsimp only
  intro hconc parent sR origin u hparent i₀ hu hmass hdrop horigin0 horigin1 hcount
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  obtain ⟨P0,hP0,hint,hpos,havg,hconst,hcompare⟩ := hpred ι κ tops T N Label Item P
    hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w hw hbranch
    hwidth hlength hzero hKb hKbL σ j M hM hMmax phase a Z A maskExponent D Nmass
    ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask hD hNmass hlogN z eta
    hetaLo hetaHi hPeta hweight htotal hconc parent sR (origin-z.1) u hparent i₀
    hu hmass hdrop (by linarith) (by
      change 0 ≤ origin-z.1+sourceLineScale g L w upper
      change z.1 ≤ origin+sourceLineScale g L w upper at horigin1
      linarith) hcount
  obtain ⟨hm,hi,hp,ha,hc⟩ := grid.snapshot_factor_transfer z.1 (upper-lower)
    P0 hP0 hint hpos havg hconst
  refine ⟨fun x => P0 (x-z.1),hm,hi,hp,ha,hc,?_⟩
  intro x hx
  have hb : x-z.1 ∈ (grid.atSnapshot z.1).root :=
    (grid.atSnapshot_mem_root z.1 x).mpr hx
  have he := hcompare (x-z.1) hb
  have heq : SlopeBox.lineShift sR (x-z.1) z = (x,z.2+sR*(x-z.1)) := by
    unfold SlopeBox.lineShift
    congr 1; ring
  rw [heq] at he
  exact he

end LipschitzHilbert.AngularGrid

end

end OAI
