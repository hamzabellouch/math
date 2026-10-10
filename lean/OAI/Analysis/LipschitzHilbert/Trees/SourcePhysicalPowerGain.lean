import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalAmplitudeMotion
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableDecay

namespace OAI

/-! The predictable amplitude estimate at the source parameters, with a
fixed dyadic power gain and no auxiliary packet-motion hypothesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem source_physical_amplitude_power_gain (p q : ℝ) (D Bslots : ℕ) (C Cfreq : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hC : 1 ≤ C) (hCfreq : 0 ≤ Cfreq) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item),
    (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
    (∀ t ∈ tops, (P t).constant ≤ L^p) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound)
      (Kw : ℝ), 1 ≤ Kw →
    (∀ t ∈ tops, SourceLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (cutoff : ι → Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (g.branching:ℝ) = SourceParameters.step L →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j, (P t).length j ≤ (T t).length) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → (Kb:ℝ) ≤ L^2 → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
    ∀ (M : ι → ℕ),
    (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
    (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
    ∀ (sR : ℝ) (cell : ℤ),
    (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
    g.width h ≤ B*g.width start →
    ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
    ∀ (z : ℝ × ℝ) (frequency : κ → ℝ),
    (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
    ∀ (phase : ℕ → ℂ) (a Z A maskExponent : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ maskExponent →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) → 0 ≤ A → A ≤ L^q →
    Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalCoefficient (T t).slope (cutoff t) v test
    let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
      (div_pos hw ((P t).length_pos j))
    let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤
        A*(weight t z)^8) →
    let value := fun zz t j => (Q t).rawBand
      (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
      zz.1 (zz.2-(T t).slope*zz.1)
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
        Prod.fst (fun p => stop p.1 p.2) (fun p => value (SlopeBox.lineShift sR b z) p.1 p.2)
        phase a (SlopeBox.lineShift sR b z) start cell-
      diagonalModulationIsometry frequency ((sR-g.center start cell)*b)
        (g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight Kb gap (tops ×ˢ (Finset.univ : Finset (Fin N)))
          Prod.fst (fun p => stop p.1 p.2) (fun p => value z p.1 p.2)
          phase a z start cell)‖ ≤
      (SourceParameters.step L)^(-(1/4:ℝ))*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight start cell z := by
  obtain ⟨Lbase,hbase1,hbaseSlots,hphysical⟩ := source_physical_amplitude_motion p D Bslots
  obtain ⟨Ldecay,hdecay⟩ := Filter.eventually_atTop.mp
    (eventually_source_predictable_coefficient p q (D:ℝ) C Cfreq hp hq (Nat.cast_nonneg D) hC hCfreq)
  refine ⟨max Lbase Ldecay, hbase1.trans (le_max_left _ _),
    hbaseSlots.trans (le_max_left _ _), ?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom cutoff v hv
    test htest htest1 g w B hw hB hbranch hwidth hlength hzero Kb hKb hK gap h start hbase
    M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq phase a Z A maskExponent
    ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal
  dsimp only
  intro hconc
  have hraw := hphysical L ((le_max_left _ _).trans hLL) ι tops T N κ Label Item P hcard hP
    alt hAlt Kw hKw hgeom cutoff v hv test htest htest1 g w B hw hB hwidth hlength hzero
    Kb hKb gap h start hbase M hM hMmax hgap sR cell hs hblock b hb z frequency Cfreq
    hCfreq hfreq hPfreq phase a Z C A maskExponent ha0 ha1 hZ hz0 hz hC htC hA hconc
  have hbudget := hdecay L ((le_max_right _ _).trans hLL) A maskExponent Kw
    (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z) a Z Kb hA hAL hmask hKw ha0 ha1 hZ hZL hK htotal
  rw [← hbranch] at hbudget
  simpa only [hbranch] using hraw.trans (mul_le_mul_of_nonneg_right hbudget
    (g.mass_nonnegative tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) (fun t zz => (T t).weight Kw (D:ℝ) zz)
      (fun t zz => ((T t).weight_pos (zero_lt_one.trans_le hKw) _ zz).le) start cell z))

end LipschitzHilbert.AngularGrid

end

end OAI
