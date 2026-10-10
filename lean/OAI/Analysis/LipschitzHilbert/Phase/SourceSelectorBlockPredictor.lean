import OAI.Analysis.LipschitzHilbert.Phase.SourceBlockPredictor
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockPathMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockPathMass
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorPhysicalMotion
import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorInsignificant
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalAmplitudeMeasurable

namespace OAI

/-! The local source predictor for the original physical packet family.
Its normalized motion and insignificant-child hypotheses are discharged
by the actual packet estimates and the snapshot concentration bounds. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

private theorem modulation_rescale {κ : Type} [Fintype κ]
    (eta : κ → ℝ) (v : EuclideanSpace ℂ κ) (d b : ℝ) :
    diagonalModulation eta v (d*b) = diagonalModulation (fun k => d*eta k) v b := by
  ext k
  have h : eta k*(d*b) = (d*eta k)*b := by ring
  simp only [diagonalModulation,WithLp.ofLp_toLp,character,h]

theorem eventually_source_selector_block_predictor
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
      origin ≤ 0 → 0 ≤ origin+grid.width →
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
            (n (SlopeBox.lineShift sR b z)) (c (SlopeBox.lineShift sR b z))
            (fun i => wave (SlopeBox.lineShift sR b z) i.val) (lam (SlopeBox.lineShift sR b z)) ≤
            Real.exp (SourceParameters.step L^(-(1/32:ℝ))*u)*Γ b := by
  obtain ⟨Lm,_,_,hmotion⟩ := source_selector_normalized_motion pProfile q Dweight Bslots
    Cweight Cfreq hpProfile hq hCweight hCfreq
  filter_upwards [eventually_ge_atTop Lm,eventually_ge_atTop (256:ℝ),
    eventually_source_block_predictor Cmass (q+6) Cfreq c0 hCmass (by linarith) hCfreq hc0,
    eventually_source_block_path_motion (Dweight:ℝ) (Nat.cast_nonneg Dweight),
    eventually_source_snapshot_envelope Cweight q (by linarith),
    eventually_source_selector_insignificant_node Cweight q hCweight,
    eventually_source_insignificant_error (q+6)]
    with L hLm hL hpred hpath hpoly hinsig hsmallError
  intro ι κ _ tops T N Label Item _ P hslots hP alt hAlt Kw hKw hgeom selector hselector hselector1 v hv
    test htest htest1 g w hw hbranch hwidth hlength hzero hKb hKbL σ j M hM hMmax
    phase a Z A maskExponent D Nmass ha0 ha1 hZ0 hZ hphase hother hreal hA0 hAq hmask
    hD hNmass hlogN z eta hetaLo hetaHi hPeta hweight htotal
  dsimp only
  let lower := ShiftedBlocks.endpoint σ j
  let upper := ShiftedBlocks.endpoint σ (j+1)
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let weight := fun t zz => (T t).weight Kw (Dweight:ℝ) zz
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalMultiplierCoefficient (T t).slope (selector t) v test
  let stop := fun t k => g.lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k))
  let wave := fun zz c => g.sourcePacketAmplitude tops slope precision cut weight
    (SourceParameters.blockCount L) (g.sourceBoundaryGap L)
    (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun p => stop p.1 p.2)
    (fun p => (Q p.1).rawBand
      (fun j l u => (T p.1).mask L maskExponent zz • coeff p.1 j l u)
      0 p.2 zz.1 (zz.2-(T p.1).slope*zz.1))
    (fun k => phase (ShiftedBlocks.tag hKb k)) a zz upper c
  intro hconc parent sR origin u hparent
  let cells := g.sourceBlockCells tops slope precision cut lower upper parent
  let n := fun zz => g.mass tops slope precision cut weight lower parent zz
  let c := fun zz (i : cells) => g.mass tops slope precision cut weight upper i.val zz
  let lam := fun zz (i : cells) => g.packetPathProduct
    (g.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) zz)
    lower upper (slope (g.sourceBlockTop tops slope precision cut lower upper parent i))
  let grid := sourceLineGrid L origin (sourceLineScale g L w upper) (upper-lower)
    (sourceLineScale_pos g L hw upper)
  intro i₀ hu hmass hdrop horigin0 horigin1 hcount
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hB : 1 ≤ SourceParameters.branching L :=
    one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hlu : lower ≤ upper := (ShiftedBlocks.endpoint_strictMono hKb σ).monotone (Nat.le_succ j)
  have hsteps : ((upper-lower:ℕ):ℝ) ≤ L^2 :=
    (Nat.cast_le.mpr (show upper-lower ≤ SourceParameters.blockCount L by
      have ht := ShiftedBlocks.endpoint_width_le σ j
      dsimp only [upper,lower]
      omega)).trans hKbL
  have hmu := source_phaseMu_small (show 1 ≤ D by linarith) hL
  have hp : 2 ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    nlinarith
  have hphase0 (k : ℕ) : 0 ≤ (phase (ShiftedBlocks.tag hKb k)).re := by
    by_cases heq : ShiftedBlocks.tag hKb k = σ
    · simpa only [heq,hreal] using hmu.1.le
    · rw [hother _ heq]
  have hwpos (t : ι) (zz : ℝ × ℝ) : 0 < weight t zz := (T t).weight_pos hKw0 _ zz
  have hprecision (t : ι) (_ : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) :=
    (P t).stopping_antitone g cut w hw (hzero t ht)
  have hmax (t : ι) (ht : t ∈ tops) (k : Fin N) : stop t k ≤ M t := by
    apply hMmax t ht
    exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hw.le ((P t).length_pos k) (hlength t ht k))
      (by positivity)).trans
      (g.eligible_lastEligible cut (w/(P t).length k) (div_pos hw ((P t).length_pos k)) (hzero t ht k))
  have hconc0 (t : ι) (ht : t ∈ tops) (l u : ℕ) (hlu : l ≤ u) (huN : u ≤ N) :
      ‖(Q t).rawInterval (coeff t) 0 l u z.1 (z.2-slope t*z.1)‖ ≤ A*(weight t z)^8 := by
    have hc := hconc t ht l u hlu huN (z.2-slope t*z.1) (by
      change |(z.2-slope t*z.1)-(z.2-slope t*z.1)| ≤ (T t).width
      rw [sub_self,abs_zero]
      exact (T t).width_pos.le)
    exact (le_add_of_nonneg_right (mul_nonneg (T t).width_pos.le (norm_nonneg _))).trans hc
  have hsize (i : cells) : ‖wave z i.val‖ ≤ L^(q+6)*c z i := by
    have he := g.source_snapshot_masked_node_bound tops slope precision cut weight hprecision hwpos
      hKb (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) M hM hMmax
      a Z ha0 ha1 hZ0 (fun _ _ k _ => hphase0 k)
      (fun _ _ k _ => hphase _) Q coeff 0 stop hstop hmax
      (fun _ => z.1) (fun t => z.2-slope t*z.1) A Cweight hA0 hCweight z hweight hconc0
      (fun t => (T t).mask L maskExponent z) upper i.val
      (fun t _ => by
        change |topSincMask L maskExponent _ _| ≤ 1
        rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
        exact topSincMask_le_one _ _ _ _)
    exact he.trans (mul_le_mul_of_nonneg_right
      (hpoly A a Z (∑ t ∈ tops, weight t z) (SourceParameters.blockCount L)
        hA0 hAq ha0 ha1 hZ0 hZ hKbL htotal)
      (g.mass_nonnegative tops slope precision cut weight (fun t zz => (hwpos t zz).le) upper i.val z))
  have hsmall (i : cells)
      (hi : ∀ t ∈ g.cellTops tops slope precision cut upper i.val,
        L^(maskExponent+2) < (T t).radius z) :
      ‖wave z i.val‖ ≤ 2*SourceParameters.step L^(-(1/8:ℝ))*c z i := by
    have he := hinsig ι tops T N κ Label Item P alt hAlt selector v test g w cut Kw
      (Dweight:ℝ) hw hKw0 hlength hzero (SourceParameters.blockCount L) hKb hKbL
      (g.sourceBoundaryGap L) (fun k => phase (ShiftedBlocks.tag hKb k)) M hM hMmax
      a Z A maskExponent ha0 ha1 hZ0 hZ hA0 hAq
      (fun _ _ k _ => hphase0 k) (fun _ _ k _ => hphase _) z hweight htotal hconc0
      upper i.val (fun t ht => (hi t ht).le)
    exact he.1.trans (mul_le_mul_of_nonneg_right
      (hsmallError.trans (by nlinarith [Real.rpow_nonneg (SourceParameters.step_pos L).le (-(1/8:ℝ))]))
      (g.mass_nonnegative tops slope precision cut weight (fun t zz => (hwpos t zz).le) upper i.val z))
  have hrep (i : cells) := g.sourceBlockTop_spec tops slope precision cut lower upper parent i
  have hchild (zz : ℝ × ℝ) (i : cells) : 0 < c zz i := by
    have he := g.path_mass_pos tops slope precision cut weight hwpos upper
      (g.sourceBlockTop tops slope precision cut lower upper parent i)
      (hrep i).1 (hrep i).2.2.1 zz
    simpa only [(hrep i).2.2.2] using he
  have hn (zz : ℝ × ℝ) : 0 < n zz := by
    have he := g.path_mass_pos tops slope precision cut weight hwpos lower
      (g.sourceBlockTop tops slope precision cut lower upper parent i₀) (hrep i₀).1
      (g.eligible_of_le (hprecision _ (hrep i₀).1) hlu (hrep i₀).2.2.1) zz
    simpa only [(hrep i₀).2.1] using he
  have hoff : (∑ i : RemainderIndex i₀, c z i/n z) ≤ u :=
    (g.sourceBlock_off_fractions tops slope precision cut weight hprecision
      (fun t zz => (hwpos t zz).le) lower upper hlu parent z (hn z) i₀).trans hdrop
  have hroot (b : ℝ) (hb : b ∈ grid.root) : |b| ≤ sourceLineScale g L w upper := by
    change origin ≤ b ∧ b < origin+sourceLineScale g L w upper at hb
    change 0 ≤ origin+sourceLineScale g L w upper at horigin1
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hroot' (b : ℝ) (hb : b ∈ grid.root) :
      |b| ≤ w/(g.width upper*Real.sqrt (g.branching:ℝ)) := by
    simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hroot b hb
  have hblock := (g.source_shifted_width_bounds L hbranch hKb σ j).2
  have hmove (b : ℝ) (hb : b ∈ grid.root) (i : cells) := by
    have hs (t : ι) (ht : t ∈ g.cellTops tops slope precision cut upper i.val) :
        g.index lower (slope t) = g.index lower sR := by
      have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
      rw [hparent,← (hrep i).2.1]
      exact g.index_eq_of_le hlu (ht'.2.1.trans (hrep i).2.2.2.symm)
    have hm := hmotion L hLm ι tops T N κ Label Item P hslots hP alt hAlt Kw hKw hgeom
      selector hselector hselector1 v hv test htest htest1 g w (SourceParameters.branching L) hw hB hbranch
      hwidth hlength hzero (SourceParameters.blockCount L) hKb hKbL (g.sourceBoundaryGap L)
      lower upper hlu M hM hMmax
      (fun _ _ k hk _ => ⟨(g.sourceBoundaryGap_pos L k).le,g.sourceBoundaryGap_le_width L hk⟩)
      sR i.val hs hblock b (hroot' b hb) z eta hetaHi hPeta
      (fun k => phase (ShiftedBlocks.tag hKb k)) a Z A maskExponent ha0 ha1 hZ0 hZ hmask
      (fun _ _ k _ => hphase0 k) (fun _ _ k _ => hphase _) hweight hA0 hAq htotal hconc
      lower le_rfl hlu hsteps (g.sourceBlockTop tops slope precision cut lower upper parent i)
      (g.sourceBlockTop_mem_child tops slope precision cut lower upper parent i)
      (Real.sqrt L) (phaseMu D (Real.sqrt L)) (by linarith) hmu.1.le (by linarith)
    dsimp only at hm
    have hi : g.index lower (T (g.sourceBlockTop tops slope precision cut lower upper parent i)).slope =
        parent := (hrep i).2.1
    rw [hi] at hm
    simpa only [modulation_rescale] using hm
  have hsizePower := source_snapshot_amplitude_scale (show 1 ≤ L by linarith) hNmass (hn z)
    hCmass (show 0 ≤ q+6 by linarith) hmu.1.le (by linarith : phaseMu D (Real.sqrt L) ≤ 1) hmass
  have ha : 0 ≤ 1-phaseMu D (Real.sqrt L)-1/Real.sqrt L := by
    have hi : 1/Real.sqrt L ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp
    linarith
  have hpdata := hpath ι g tops T w Kw hw hKw hbranch hwidth hKb σ j hsteps
    phase Z (phaseMu D (Real.sqrt L)) (Real.sqrt L) u hZ0 hZ hphase hother hreal
    hmu.1.le (by linarith) (by linarith) ha hu
    (g.sourceBlockTop tops slope precision cut lower upper parent i₀)
    (hrep i₀).1 (hrep i₀).2.2.1 sR ((hrep i₀).2.1.trans hparent.symm) z
  dsimp only at hpdata
  rw [(hrep i₀).2.1,(hrep i₀).2.2.2] at hpdata
  obtain ⟨err,herr0,herr1,herrε,hlam0,hcoef0,hcoef1,hdef,hpathMove⟩ := hpdata hdrop
  apply hpred D Nmass hD hNmass hlogN ι κ g hbranch hKb σ j tops T w hw weight hwpos
    parent z origin sR eta hetaLo hetaHi phase hother hreal i₀ (fun i => wave z i.val)
    (L^(maskExponent+2)) u err hu hmass hsize hoff hsmall hcount
    (fun b => n (SlopeBox.lineShift sR b z))
    (fun b => c (SlopeBox.lineShift sR b z))
    (fun b i => wave (SlopeBox.lineShift sR b z) i.val)
    (fun b => lam (SlopeBox.lineShift sR b z))
    (fun b _ => hn _) (fun b _ i => hchild _ i)
  · intro b hb i
    exact (hmove b hb i).1
  · intro b hb i
    exact (hmove b hb i).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsizePower.1
        (Real.rpow_nonneg (SourceParameters.step_pos L).le _))
      (div_pos (hchild z i) (hn z)).le)
  · intro _
    exact ⟨hlam0,herr0,herr1,herrε,hcoef0,hcoef1,hdef,
      fun b hb => (hpathMove b (hroot b hb)).1,
      fun b hb => (hpathMove b (hroot b hb)).2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
