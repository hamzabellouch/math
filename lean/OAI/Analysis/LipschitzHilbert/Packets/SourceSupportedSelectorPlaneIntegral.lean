import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedSelectorMarkedIntegral
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorPlaneIntegral

namespace OAI

/-! Original-selector marked bounds pass from each terminal line window
 to the plane. The measurable integrand is the original active path;
 the locally chosen marked factors need no joint measurability. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

namespace AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem eventually_source_supported_selector_plane_integral
    (pProfile q Cmass Cweight Cfreq c0 A_M : ℝ) (Dweight Bslots : ℕ)
    (hpProfile : 0 ≤ pProfile) (hq : 0 ≤ q) (hCmass : 0 ≤ Cmass)
    (hCweight : 1 ≤ Cweight) (hCfreq : 0 ≤ Cfreq) (hc0 : 0 < c0)
    (hAM : 0 ≤ A_M) (hDweight : 2 < (Dweight:ℝ)) :
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
    ∀ (top : ι), top ∈ tops →
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length) 0 →
    ∀ (good : Set (ℝ×ℝ)), MeasurableSet good →
    ∀ (active : ℝ×ℝ → ℝ), Measurable active →
      (∀ z ∈ good, 0 ≤ active z) →
    ∀ (Cpath : ℝ), 0 ≤ Cpath →
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
    let H := sourceLineScale g L w (ShiftedBlocks.endpoint σ count)
    let grid := fun k : ℤ => sourceReverseLineGrid g L (H*k) hw σ count
    let n := fun y x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
    let beta := fun y j x => g.sourceShiftedPathPrediction tops slope precision cut weight
      (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
      (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
      σ top (x,y+slope top*x) j
    let marked := fun k y j i => sourceMarkedCell
      ((grid k).cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
      (fun x => n y x j) (fun x => n y x j-n y x (j+1)) (L^A_M)
    (∀ z ∈ good, ∀ t ∈ tops, weight t z ≤ Cweight) →
    (∀ z ∈ good, Real.log (max 1 (∑ t ∈ tops, weight t z)) ≤ 3*L) →
    (∀ z ∈ good, (∑ t ∈ tops, weight t z) ≤ L^Cmass*Nmass) →
    (∀ z ∈ good, ∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ yy,
      |yy-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 yy‖+(T t).width*
        ‖covariantSignal (P t).frequency (fun k zz => (Q t).rawInterval (coeff t) 0 l u z.1 zz k) yy‖ ≤
          A*(weight t z)^8) →
    (∀ j < count, ∀ z ∈ good, ∀ I : Finset ι, I ⊆ tops →
      (∀ t ∈ I, (T t).radius z ≤ L^(maskExponent+2)) →
      (∀ t ∈ I, precision t ≤ g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))/
        (SourceParameters.branching L)^2) →
      (∀ t ∈ I, ∀ v ∈ I, |slope t-slope v| ≤ SourceParameters.branching L*
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) →
      (∀ t ∈ I, ∀ v ∈ I, t ≠ v →
        g.sourceGap L (ShiftedBlocks.endpoint σ (j+1)) ≤ |slope t-slope v|) →
      (I.card:ℝ) ≤ D/100) →
    (∀ (k : ℤ) (y x : ℝ), x ∈ (grid k).root → (x,y+slope top*x) ∈ good →
      active (x,y+slope top*x) ≤ Cpath*
        ∏ j ∈ Finset.range count, reverseMarkedValue (grid k) (ShiftedBlocks.reverseLevel σ count)
          count (marked k y) (beta y) j x) →
    Integrable (good.indicator (fun z => weight top z*active z)) (volume.prod volume) ∧
      (∫ z, good.indicator (fun z => weight top z*active z) z ∂volume.prod volume) ≤
        ((Cpath*(Real.exp 1*Real.exp (2*(Dweight:ℝ))))*
          (2^(Dweight:ℝ)*∫ z, topProfile (Dweight:ℝ) z ∂volume.prod volume))*
            Kw^2*(T top).length*(T top).width := by
  filter_upwards [eventually_source_supported_selector_marked_integral pProfile q Cmass Cweight Cfreq c0 A_M
    Dweight Bslots hpProfile hq hCmass hCweight hCfreq hc0 hAM] with L hmarked
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN eta hetaLo hetaHi hPeta top htop htop0 good hgood active hactive
    hactive0 Cpath hCpath
  dsimp only
  intro hweight htotal hmass hconc hcount hpath
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let count := g.firstIneligibleShiftedBlock cut (precision top)
    (div_pos hw (T top).length_pos) hKb σ
  let H := sourceLineScale g L w (ShiftedBlocks.endpoint σ count)
  let grid := fun k : ℤ => sourceReverseLineGrid g L (H*k) hw σ count
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let value := fun zz (p : ι × Fin N) => (Q p.1).rawBand
    (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
    0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1)
  let n := fun y x => g.shiftedPathMass tops slope precision cut weight σ top (x,y+slope top*x)
  let beta := fun y j x => g.sourceShiftedPathPrediction tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2) value
    (fun k => phase (ShiftedBlocks.tag hKb k)) a (Real.sqrt L) (phaseMu D (Real.sqrt L))
    σ top (x,y+slope top*x) j
  let marked := fun k y j i => sourceMarkedCell
    ((grid k).cell (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) i)
    (fun x => n y x j) (fun x => n y x j-n y x (j+1)) (L^A_M)
  let f := good.indicator (fun z => weight top z*active z)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hfmeas : Measurable f :=
    (((T top).continuous_weight hKw0 _).measurable.mul hactive).indicator hgood
  have hf0 (z : ℝ×ℝ) : 0 ≤ f z :=
    indicator_nonneg (fun z hz => mul_nonneg ((T top).weight_pos hKw0 _ z).le
      (hactive0 z hz)) z
  apply source_plane_area_bound (T top) hKw0 hDweight (slope top) H
    (Cpath*(Real.exp 1*Real.exp (2*(Dweight:ℝ))))
    (sourceLineScale_pos g L hw _) f hfmeas.aestronglyMeasurable hf0
  apply Filter.Eventually.of_forall
  intro y k
  let goodLine : Set ℝ := {x | (x,y+slope top*x) ∈ good}
  have hgoodLine : MeasurableSet goodLine := hgood.preimage (by fun_prop)
  have hroot : (grid k).root = sourceLineTile H k :=
    finiteLineGrid_root_tile (grid k) k rfl
  have hl := hmarked ι κ tops T N Label Item P hslots hP alt hAlt Kw hKw hgeom
    selector hselector hselector1 v hv test htest htest1 g w hw hbranch hwidth hlength hzero
    hKb hKbL σ M hM hMmax phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase
    hother hreal hA0 hAq hmask hD hNmass hlogN eta hetaLo hetaHi hPeta top htop htop0
    (H*k) y goodLine hgoodLine
    (fun x hx => hweight _ hx) (fun x hx => htotal _ hx) (fun x hx => hmass _ hx)
    (fun x hx => hconc _ hx) (fun j hj x hx => hcount j hj _ hx)
  change IntegrableOn (goodLine.indicator (fun x => weight top (x,y+slope top*x)*
      ∏ j ∈ Finset.range count, reverseMarkedValue (grid k) (ShiftedBlocks.reverseLevel σ count)
        count (marked k y) (beta y) j x)) (grid k).root volume ∧ _ at hl
  rw [hroot] at hl
  have ha : Measurable (fun x => active (x,y+slope top*x)) := hactive.comp (by fun_prop)
  have hwmeas : Measurable (fun x => weight top (x,y+slope top*x)) :=
    (T top).continuous_weight hKw0 (Dweight:ℝ) |>.comp (by fun_prop) |>.measurable
  have ht := source_path_integral_transfer_on volume (sourceLineTile H k) goodLine
    (sourceLineTile_measurable H k) (fun x => weight top (x,y+slope top*x))
    (fun x => active (x,y+slope top*x))
    (fun x => ∏ j ∈ Finset.range count,
      reverseMarkedValue (grid k) (ShiftedBlocks.reverseLevel σ count)
        count (marked k y) (beta y) j x)
    Cpath (Real.exp 1*Real.exp (2*(Dweight:ℝ))) hCpath
    (fun x => ((T top).weight_pos hKw0 _ _).le)
    (fun x hx => hactive0 _ hx)
    ((hwmeas.mul ha).indicator hgoodLine).aestronglyMeasurable
    hl.1 hl.2 (fun x hx hxgood => hpath k y x (hroot.symm ▸ hx) hxgood)
  have hindicator : goodLine.indicator (fun x =>
      weight top (x,y+slope top*x)*active (x,y+slope top*x)) =
        fun x => f (x,y+slope top*x) := by
    funext x
    rfl
  rw [hindicator] at ht
  exact ht

end AngularGrid
end LipschitzHilbert

end

end OAI
