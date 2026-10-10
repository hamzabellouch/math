import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedSelectorIntervalMotion
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalNormalizedMotion
import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedBandStops

namespace OAI

/-! Source motion only requires shortness for actual packet items. Empty
long bands have unchanged amplitude when their formal stops are clipped.
The original coefficients, scale parameters and conclusions are retained. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem source_supported_selector_amplitude_motion (p : ℝ) (D Bslots : ℕ) :
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
    (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(P t).length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb → ∀ (gap : ℕ → ℝ) (h start : ℕ), h ≤ start →
    ∀ (M : ι → ℕ),
    (∀ t ∈ tops, g.eligible (g.rootWidth/B^2) (w/(T t).length) (M t)) →
    (∀ t ∈ tops, ∀ j, g.eligible (g.rootWidth/B^2) (w/(T t).length) j → j ≤ M t) →
    (∀ t ∈ tops, ∀ j, h ≤ j → j ≤ M t → 0 ≤ gap j ∧ gap j ≤ g.width h) →
    ∀ (sR : ℝ) (cell : ℤ),
    (∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) start cell, g.index h (T t).slope = g.index h sR) →
    g.width h ≤ B*g.width start →
    ∀ (b : ℝ), |b| ≤ w/(g.width start*Real.sqrt (g.branching:ℝ)) →
    ∀ (z : ℝ × ℝ) (frequency : κ → ℝ) (Cfreq : ℝ), 0 ≤ Cfreq →
    (∀ k, |frequency k| ≤ Cfreq/w) → (∀ t ∈ tops, (P t).frequency = frequency) →
    ∀ (phase : ℕ → ℂ) (a Z C A maskExponent : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ Z →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    1 ≤ C → (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) → 0 ≤ A →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
      (div_pos hw ((P t).length_pos j))
    let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤
        A*(weight t z)^8) →
    let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
      (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
    let δ := (5*(D:ℝ)/Kw)/Real.sqrt (g.branching:ℝ)
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*Kb)*(Real.log (max 1 (∑ t ∈ tops, weight t z))+1))^2
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
      (V*((1+d)*(J/Real.sqrt (g.branching:ℝ))+d*A)*C^3)*
        g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
          (g.rootWidth/B^2) weight start cell z := by
  obtain ⟨L0,hL0,hslots,hpacket⟩ :=
    SourceLabeledLattice.source_selector_predictable_masked_interval_motion_of_supported p D Bslots
  refine ⟨L0,hL0,hslots,?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w B hw hB hwidth hlength hzero Kb hKb gap h start hbase M hM
    hMmax hgap sR cell hs hblock b hb z frequency Cfreq hCfreq hfreq hPfreq phase a Z C A
    maskExponent ha0 ha1 hZ hz0 hz hC htC hA
  dsimp only
  intro hconc
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
  let z' := SlopeBox.lineShift sR b z
  let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
    (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
  have hL : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hsupported : ∀ t ∈ tops, ∀ j (l : (Q t).labels j) (_u : Item j l),
      rawStop t j ≤ M t := by
    intro t ht j l u
    exact g.source_length_stop_le_of_item tops T P w (g.rootWidth/B^2) hw M
      hzero hlength hMmax t ht j l u
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    intro i j hij
    exact min_le_min ((P t).stopping_antitone g (g.rootWidth/B^2) w hw (hzero t ht) hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hmasked (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (hu : u ≤ N) :
      ‖(Q t).rawInterval (fun j k v => (T t).mask L maskExponent z • coeff t j k v)
        0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤ A*(weight t z)^8 := by
    rw [(Q t).rawInterval_coeff_smul, norm_smul, Real.norm_eq_abs]
    have hmask : |(T t).mask L maskExponent z| ≤ 1 := by
      change |topSincMask L maskExponent _ _| ≤ 1
      rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
      exact topSincMask_le_one _ _ _ _
    have hc := hconc t ht l u hlu hu (z.2-(T t).slope*z.1) (by simp [(T t).width_pos.le])
    have hraw : ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-(T t).slope*z.1)‖ ≤
        A*(weight t z)^8 := by
      exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc
    exact (mul_le_mul_of_nonneg_right hmask (norm_nonneg _)).trans (by simpa using hraw)
  have heq (zz : ℝ×ℝ) := g.sourceBandAmplitude_clip_stop tops
    (fun t => (T t).slope) (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap Q
    (fun t j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 rawStop M hsupported
    (fun _ => zz.1) (fun t => zz.2-(T t).slope*zz.1) phase a zz start cell
  rw [heq z',heq z]
  apply g.source_node_predictable_motion tops T w B Kw (D:ℝ) hw hB hKw0
    (Nat.cast_nonneg D) hwidth hKb gap h start hbase M hM hMmax hgap sR cell hs
    (g.width start) (g.width_pos start) hblock b hb z phase a Z C ha0 ha1 hZ hz0 hz hC htC
    Q (fun t j l u => (T t).mask L maskExponent z • coeff t j l u)
    (fun t j l u => (T t).mask L maskExponent z' • coeff t j l u)
    0 stop hstop hmax (fun _ => z.1) (fun t => z.2-(T t).slope*z.1)
    (fun _ => z'.1) (fun t => z'.2-(T t).slope*z'.1) A (J/Real.sqrt (g.branching:ℝ))
    (diagonalModulationIsometry frequency ((sR-g.center start cell)*b)) hA
    (by positivity) hmasked
  intro t ht l u hlu hu hactive
  obtain ⟨htt,hcell,hel⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
  obtain ⟨_,_,_,hbx,hby⟩ := g.source_packet_displacement_ratios (T t) hw hB
    (hwidth t htt) h start sR b (hs t ht).symm hblock hel hb
  have hf : ∀ k, |(P t).frequency k| ≤ Cfreq/w := by rw [hPfreq t htt]; exact hfreq
  have hm := (hpacket L hLL N κ Label Item (P t) (hcard t htt) (hP t htt)
    (alt t) (hAlt t) (T t) Kw hKw (hgeom t htt) (selector t) (hselector t) (hselector1 t) v hv test htest htest1
    g w B hw hB0 (hzero t htt) start l u hlu
    (fun j hjl hju => (hactive j hjl hju).trans (min_le_left _ _)) sR (g.center start cell) b A
    maskExponent (Cfreq/w) z (by positivity) hf hbx hby (hconc t htt l u hlu hu)).2
  have hbudget := g.source_packet_motion_coefficient (T t) hw hB hL hA hCfreq le_rfl
    (hwidth t htt) h start sR b (hs t ht).symm hblock hel hb p maskExponent (D:ℝ)
  rw [hcell] at hbudget
  rw [hPfreq t htt] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right hbudget (pow_nonneg ((T t).weight_pos hKw0 _ z).le 8))


theorem source_supported_selector_amplitude_power_gain (p q : ℝ) (D Bslots : ℕ) (C Cfreq : ℝ)
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
    (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (g.branching:ℝ) = SourceParameters.step L →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
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
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
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
  obtain ⟨Lbase,hbase1,hbaseSlots,hphysical⟩ := source_supported_selector_amplitude_motion p D Bslots
  obtain ⟨Ldecay,hdecay⟩ := Filter.eventually_atTop.mp
    (eventually_source_predictable_coefficient p q (D:ℝ) C Cfreq hp hq (Nat.cast_nonneg D) hC hCfreq)
  refine ⟨max Lbase Ldecay, hbase1.trans (le_max_left _ _),
    hbaseSlots.trans (le_max_left _ _), ?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w B hw hB hbranch hwidth hlength hzero Kb hKb hK gap h start hbase
    M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq phase a Z A maskExponent
    ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal
  dsimp only
  intro hconc
  have hraw := hphysical L ((le_max_left _ _).trans hLL) ι tops T N κ Label Item P hcard hP
    alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w B hw hB hwidth hlength hzero
    Kb hKb gap h start hbase M hM hMmax hgap sR cell hs hblock b hb z frequency Cfreq
    hCfreq hfreq hPfreq phase a Z C A maskExponent ha0 ha1 hZ hz0 hz hC htC hA hconc
  have hbudget := hdecay L ((le_max_right _ _).trans hLL) A maskExponent Kw
    (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z) a Z Kb hA hAL hmask hKw ha0 ha1 hZ hZL hK htotal
  rw [← hbranch] at hbudget
  simpa only [hbranch] using hraw.trans (mul_le_mul_of_nonneg_right hbudget
    (g.mass_nonnegative tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) (fun t zz => (T t).weight Kw (D:ℝ) zz)
      (fun t zz => ((T t).weight_pos (zero_lt_one.trans_le hKw) _ zz).le) start cell z))


theorem source_supported_selector_normalized_motion (p q : ℝ) (D Bslots : ℕ) (C Cfreq : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hC : 1 ≤ C) (hCfreq : 0 ≤ Cfreq) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots:ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (ι : Type) (tops : Finset ι) (T : ι → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → SourceLabeledLattice N κ Label Item),
    (∀ t ∈ tops, ∀ j, ((P t).labels j).card ≤ Bslots) →
    (∀ t ∈ tops, (P t).constant ≤ L^p) →
    ∀ (alt : ∀ t j (l : (P t).labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
      (hAlt : ∀ t j l u k, planarProfileConstant (alt t j l u k) (2*(P t).order) ≤
        (P t).profileBound) (Kw : ℝ), 1 ≤ Kw →
    (∀ t ∈ tops, SourceSupportedLabeledTopGeometry (P t) (T t) Kw D) →
    ∀ (selector : ∀ t j, (P t).labels j → κ → ℝ → ℂ),
    (∀ t j l k, Measurable (selector t j l k)) →
    (∀ t j l k s, ‖selector t j l k s‖ ≤ 1) →
    ∀ (v : ℝ × ℝ → ℝ), Measurable v →
    ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable test → (∀ z, ‖test z‖ ≤ 1) →
    ∀ (g : AngularGrid) (w B : ℝ) (hw : 0 < w), 1 ≤ B →
    (g.branching:ℝ) = SourceParameters.step L →
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j (l : (P t).labels j) (_u : Item j l),
      (P t).length j ≤ (T t).length) →
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
    ∀ (phase : ℕ → ℂ) (a Z A maskExponent : ℝ),
    0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 ≤ maskExponent →
    (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
    (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    (∀ t ∈ tops, (T t).weight Kw (D:ℝ) z ≤ C) →
    0 ≤ A → A ≤ L^q →
    Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw (D:ℝ) z)) ≤ 3*L →
    let Q := fun t => (P t).withProfile (alt t) (hAlt t)
    let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
    let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
      (div_pos hw ((P t).length_pos j))
    let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
    (∀ t ∈ tops, ∀ l u, l ≤ u → u ≤ N → ∀ y,
      |y-(z.2-(T t).slope*z.1)| ≤ (T t).width →
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 y‖+(T t).width*
        ‖covariantSignal (P t).frequency
          (fun k yy => (Q t).rawInterval (coeff t) 0 l u z.1 yy k) y‖ ≤
        A*(weight t z)^8) →
    ∀ (lower : ℕ), h ≤ lower → lower ≤ start → ((start-lower:ℕ):ℝ) ≤ L^2 →
    ∀ (top : ι), top ∈ g.cellTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) start cell →
    ∀ (r μ : ℝ), 1 ≤ r → 0 ≤ μ → μ ≤ 1 →
    let value := fun zz t j => (Q t).rawBand
      (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
      zz.1 (zz.2-(T t).slope*zz.1)
    let amplitude := fun zz => g.sourcePacketAmplitude tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap
      (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
      (fun p => value zz p.1 p.2) phase a zz start cell
    let parentMass := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight lower (g.index lower (T top).slope) zz
    let childMass := fun zz => g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
      (g.rootWidth/B^2) weight start cell zz
    let lam := fun zz => g.packetPathProduct (g.sourceTransition tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap phase zz)
      lower start (T top).slope
    let z' := SlopeBox.lineShift sR b z
    let carrier := (sR-g.center start cell)*b
    (‖massPowerScale (parentMass z') (childMass z') (-(1/r)) (μ-1+1/r) • amplitude z'-
        diagonalModulation frequency
          (massPowerScale (parentMass z) (childMass z) (-(1/r)) (μ-1+1/r) • amplitude z)
          carrier‖ ≤
      SourceParameters.step L^(-(1/8:ℝ))*(childMass z/parentMass z)^(1/r)*(childMass z)^μ) ∧
    (‖(((parentMass z')^(μ-1):ℝ):ℂ) • (lam z' • amplitude z')-
        (((parentMass z)^(μ-1):ℝ):ℂ) •
          (lam z • diagonalModulation frequency (amplitude z) carrier)‖ ≤
      SourceParameters.step L^(-(1/8:ℝ))*(parentMass z)^μ*(childMass z/parentMass z)) := by
  obtain ⟨Lp,hLp,hSlots,hphysical⟩ := source_supported_selector_amplitude_power_gain p q D Bslots C Cfreq
    hp hq hC hCfreq
  obtain ⟨Ln,hnormal⟩ := eventually_atTop.mp
    (eventually_source_normalized_motion (D:ℝ) (q+6) (Nat.cast_nonneg D) (by linarith))
  obtain ⟨Ls,hsnapshot⟩ := eventually_atTop.mp (eventually_source_snapshot_envelope C q (by linarith))
  refine ⟨max Lp (max Ln Ls),hLp.trans (le_max_left _ _),hSlots.trans (le_max_left _ _),?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w B hw hB hbranch hwidth hlength hzero Kb hKb hKbL gap h start hbase
    M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq phase a Z A maskExponent
    ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal
  dsimp only
  intro hconc lower hhlower hlower hsteps top htopCell r μ hr hμ0 hμ1
  have hLnL : Ln ≤ L := (le_max_left Ln Ls).trans ((le_max_right Lp _).trans hLL)
  have hLsL : Ls ≤ L := (le_max_right Ln Ls).trans ((le_max_right Lp _).trans hLL)
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cutoff0 := g.rootWidth/B^2
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let rawStop := fun t j => g.lastEligible cutoff0 (w/(P t).length j) (div_pos hw ((P t).length_pos j))
  let stop := fun t j => min (rawStop t j) (M t)
  let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
  let value := fun zz t j => (Q t).rawBand
    (fun j l u => (T t).mask L maskExponent zz • coeff t j l u) 0 j
    zz.1 (zz.2-slope t*zz.1)
  let amplitude := fun zz => g.sourcePacketAmplitude tops slope precision cutoff0 weight Kb gap
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => rawStop p.1 p.2)
    (fun p => value zz p.1 p.2) phase a zz start cell
  let n := fun zz => g.mass tops slope precision cutoff0 weight lower (g.index lower (slope top)) zz
  let c := fun zz => g.mass tops slope precision cutoff0 weight start cell zz
  let lam := fun zz => g.packetPathProduct (g.sourceTransition tops slope precision cutoff0 weight Kb gap phase zz)
    lower start (slope top)
  let z' := SlopeBox.lineShift sR b z
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hprec (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hKw0 _ zz
  obtain ⟨htop,hindex,heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp htopCell
  have htopM : start ≤ M top := hMmax top htop start heligible
  have hn (zz : ℝ × ℝ) : 0 < n zz :=
    g.path_mass_pos tops slope precision cutoff0 weight hwpos lower top htop
      (g.eligible_of_le (hprec top htop) hlower heligible) zz
  have hc (zz : ℝ × ℝ) : 0 < c zz :=
    g.mass_pos_of_member tops slope precision cutoff0 weight hwpos start cell zz htopCell
  have hlog (level : ℕ) (hlevel : h ≤ level) (helevel : g.eligible cutoff0 (precision top) level) :
      |Real.log (g.mass tops slope precision cutoff0 weight level (g.index level (slope top)) z')-
        Real.log (g.mass tops slope precision cutoff0 weight level (g.index level (slope top)) z)| ≤
        (5*(D:ℝ)/Kw)/Real.sqrt (SourceParameters.step L) := by
    have he := g.boundary_submass_source_motion tops T w B Kw (D:ℝ) hw hB hKw0
      (Nat.cast_nonneg D) hwidth 0 h level hlevel 0 (by norm_num) (g.width_pos h).le
      (slope top) sR (hs top htopCell) (g.width start) (g.width_pos start) hblock
      (g.cellTops tops slope precision cutoff0 level (g.index level (slope top)))
      ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,helevel⟩⟩
      (g.parent_subset_boundary tops slope precision cutoff0 0 level 0 (slope top)) b hb z
    simpa only [hbranch,mass,weight,z'] using he
  have hN := hlog lower hhlower (g.eligible_of_le (hprec top htop) hlower heligible)
  have hchild := hlog start hbase heligible
  rw [hindex] at hchild
  have hgapBlock (j : ℕ) (hj : j ∈ Finset.Ico lower start) :
      0 ≤ gap j ∧ gap j ≤ g.width h := hgap top htop j
        (hhlower.trans (Finset.mem_Ico.mp hj).1) ((Finset.mem_Ico.mp hj).2.le.trans htopM)
  have hphaseBlock (j : ℕ) (hj : j ∈ Finset.Ico lower start) : ‖phase j‖ ≤ Z :=
    hz top htop j ((Finset.mem_Ico.mp hj).2.trans_le htopM)
  have hlamMove := g.source_block_transition_relative_motion tops T w B Kw (D:ℝ)
    hw hB hKw0 (Nat.cast_nonneg D) hwidth hKb gap phase h lower start hhlower hgapBlock
    top htop heligible sR (hs top htopCell) (g.width start) (g.width_pos start) hblock b hb z
    Z hZ hphaseBlock
  rw [hbranch] at hlamMove
  have hlam0 : lam z ≠ 0 := g.source_path_product_ne_zero tops slope precision cutoff0 weight
    Kb gap phase z lower start (slope top)
  have hlam : ‖lam z‖ ≤ 1 := g.source_path_product_norm_le_one tops slope precision cutoff0 weight
    hprec hwpos hKb gap phase z lower start top htop heligible
      (fun j hj => hz0 top htop j ((Finset.mem_Ico.mp hj).2.trans_le htopM))
  have hraw := hphysical L ((le_max_left _ _).trans hLL) ι tops T N κ Label Item P hcard hP
    alt hAlt Kw hKw hgeom selector hselector hselector1 v hv test htest htest1 g w B hw hB hbranch hwidth hlength hzero
    Kb hKb hKbL gap h start hbase M hM hMmax hgap sR cell hs hblock b hb z frequency hfreq hPfreq
    phase a Z A maskExponent ha0 ha1 hZ hZL hmask hz0 hz htC hA hAL htotal hconc
  have hsupported : ∀ t ∈ tops, ∀ j (l : (Q t).labels j) (_u : Item j l),
      rawStop t j ≤ M t := by
    intro t ht j l u
    exact g.source_length_stop_le_of_item tops T P w (cutoff0) hw M
      hzero hlength hMmax t ht j l u
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) := by
    intro i j hij
    exact min_le_min ((P t).stopping_antitone g (cutoff0) w hw (hzero t ht) hij) le_rfl
  have hmax (t : ι) (_ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := min_le_right _ _
  have hinterval (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (hu : u ≤ N) :
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-slope t*z.1)‖ ≤ A*(weight t z)^8 := by
    have hb0 := hconc t ht l u hlu hu (z.2-slope t*z.1)
      (by simpa only [slope,sub_self,abs_zero] using (T t).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hb0
  have hmaskBound (t : ι) (_ht : t ∈ tops) : |(T t).mask L maskExponent z| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hsnap := g.source_snapshot_masked_node_bound tops slope precision cutoff0 weight hprec hwpos
    hKb gap phase M hM hMmax a Z ha0 ha1 hZ hz0 hz Q coeff 0 stop hstop hmax
    (fun _ => z.1) (fun t => z.2-slope t*z.1) A C hA hC z htC hinterval
    (fun t => (T t).mask L maskExponent z) start cell hmaskBound
  have heq := g.sourceBandAmplitude_clip_stop tops slope precision cutoff0 weight Kb gap Q
    (fun t j l u => (T t).mask L maskExponent z • coeff t j l u) 0 rawStop M hsupported
    (fun _ => z.1) (fun t => z.2-slope t*z.1) phase a z start cell
  rw [← heq] at hsnap
  have henv := hsnapshot L hLsL
    A a Z (∑ t ∈ tops, weight t z) Kb hA hAL ha0 ha1 hZ hZL hKbL htotal
  have hsnapPoly : ‖amplitude z‖ ≤ L^(q+6)*c z :=
    hsnap.trans (mul_le_mul_of_nonneg_right henv (hc z).le)
  have hnormalL := hnormal L hLnL
  exact hnormalL κ Kw r μ (n z) (n z') (c z) (c z') (start-lower) Z hKw hr hμ0 hμ1
    (hn z) (hn z') (hc z) (hc z') hsteps hZ hZL frequency ((sR-g.center start cell)*b)
    (amplitude z) (amplitude z') (lam z) (lam z') hlam0 hlam hN hchild hsnapPoly hraw hlamMove


end LipschitzHilbert.AngularGrid

end

end OAI
