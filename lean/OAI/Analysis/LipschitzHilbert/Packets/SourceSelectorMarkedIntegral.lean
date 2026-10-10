import OAI.Analysis.LipschitzHilbert.Phase.SourceSelectorReversePathPredictor
import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseMarkedIntegral

namespace OAI

/-! The original masked physical packet predictor has a uniform marked
path integral on each terminal root interval. All cell factors and their
normalizations are constructed from the physical data. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_selector_marked_integral
    (pProfile q Cmass Cweight Cfreq c0 A_M : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0)
    (hAM : 0 ≤ A_M) :
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
      (∀ t ∈ tops, SourceLabeledTopGeometry (P t) (T t) Kw Dweight) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w : ℝ) (hw : 0 < w),
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
      (∀ t ∈ tops, ∀ j, (P t).length j ≤ (T t).length) →
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
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length) 0 →
    ∀ (origin y : ℝ) (good : Set ℝ), MeasurableSet good →
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
    IntegrableOn (good.indicator (fun x => weight top (x,y+slope top*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid (ShiftedBlocks.reverseLevel σ count)
        count marked beta j x)) grid.root volume ∧
    (∫ x in grid.root, good.indicator (fun x => weight top (x,y+slope top*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue grid (ShiftedBlocks.reverseLevel σ count)
        count marked beta j x) x) ≤
      Real.exp 1*Real.exp (2*(Dweight:ℝ))*∫ x in grid.root, weight top (x,y+slope top*x) := by
  filter_upwards [eventually_source_selector_reverse_path_predictor pProfile q Cmass Cweight Cfreq c0 A_M
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0,
    eventually_source_reverse_marked_integral (Dweight:ℝ) Cmass A_M (by positivity) hCmass hAM,
    eventually_ge_atTop (1:ℝ)] with L hpred hint hL
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN eta hetaLo hetaHi hPeta top htop htop0 origin y good hgood
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
  have hvv (p : ι × Fin N) : Measurable (fun zz => value zz p) :=
    ((Q p.1).masked_rawBand_continuous (coeff p.1) (T p.1) L maskExponent 0 p.2).measurable
  have hwm (t : ι) : Measurable (weight t) :=
    ((T t).continuous_weight (zero_lt_one.trans_le hKw) _).measurable
  have hwp (t : ι) (z : ℝ × ℝ) : 0 < weight t z :=
    (T t).weight_pos (zero_lt_one.trans_le hKw) _ z
  have hbeta (j : ℕ) : Measurable (beta j) :=
    (g.sourceShiftedPathPrediction_measurable tops slope precision cut weight hwm
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      value hvv (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L)
      (phaseMu D (Real.sqrt L)) σ top j).comp (by fun_prop)
  have hlogroot : Real.log (Real.sqrt Nmass) ≤ 2*L := by
    rw [Real.log_sqrt hNmass.le]
    linarith
  apply hint ι g tops T w Kw hw hKw hbranch hwidth hKb σ top htop htop0 origin y
    (Real.sqrt Nmass) (Real.sqrt_pos.mpr hNmass) hlogroot good hgood beta hbeta
  · intro x _hx j hj
    have he := g.eligible_before_firstIneligibleShiftedBlock cut (precision top)
      (div_pos hw (T top).length_pos) hKb σ hj
    exact (g.sourceShiftedPathPrediction_pos tops slope precision cut weight hwp
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      value (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L)
      (phaseMu D (Real.sqrt L)) σ top htop (x,y+slope top*x) j he).le
  · intro j hj
    obtain ⟨Γ,_hmeas,hpos,hconst,havg,_hone,hcomp⟩ := hpred ι κ tops T N Label Item P
      hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w hw hbranch hwidth
      hlength hzero hKb hKbL σ M hM hMmax phase a Z A maskExponent D Nmass
      ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask hD hNmass hlogN eta hetaLo
      hetaHi hPeta top htop origin y good hweight htotal hmass hconc hcount j hj
    exact ⟨Γ,hpos,hconst,havg,hcomp⟩
  · intro x hx
    simpa only [Real.sq_sqrt hNmass.le] using hmass x hx

end LipschitzHilbert.AngularGrid

end

end OAI
