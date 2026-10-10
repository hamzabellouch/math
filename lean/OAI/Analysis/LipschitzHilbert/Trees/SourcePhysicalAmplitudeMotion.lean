import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableAmplitudeMotion
import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketMotionBudget

namespace OAI

/-! Predictable motion for the original physical coefficients, original
length stopping, actual top masks, and actual angular masses. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem source_physical_amplitude_motion (p : ℝ) (D Bslots : ℕ) :
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
    (∀ t ∈ tops, B^2*w ≤ (T t).width) →
    (∀ t ∈ tops, ∀ j, (P t).length j ≤ (T t).length) →
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
    SourceLabeledLattice.source_predictable_masked_interval_motion p D Bslots
  refine ⟨L0,hL0,hslots,?_⟩
  intro L hLL ι tops T N κ Label Item _ _ P hcard hP alt hAlt Kw hKw hgeom cutoff v hv
    test htest htest1 g w B hw hB hwidth hlength hzero Kb hKb gap h start hbase M hM
    hMmax hgap sR cell hs hblock b hb z frequency Cfreq hCfreq hfreq hPfreq phase a Z C A
    maskExponent ha0 ha1 hZ hz0 hz hC htC hA
  dsimp only
  intro hconc
  let Q := fun t => (P t).withProfile (alt t) (hAlt t)
  let coeff := fun t => (P t).physicalCoefficient (T t).slope (cutoff t) v test
  let stop := fun t j => g.lastEligible (g.rootWidth/B^2) (w/(P t).length j)
    (div_pos hw ((P t).length_pos j))
  let weight := fun t zz => (T t).weight Kw (D:ℝ) zz
  let z' := SlopeBox.lineShift sR b z
  let J := L^(2*p+4)*Real.exp (16*(D:ℝ))+A+
    (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
  have hL : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hstop (t : ι) (ht : t ∈ tops) : Antitone (stop t) :=
    (P t).stopping_antitone g (g.rootWidth/B^2) w hw (hzero t ht)
  have hmax (t : ι) (ht : t ∈ tops) (j : Fin N) : stop t j ≤ M t := by
    apply hMmax t ht
    have hj := g.eligible_lastEligible (g.rootWidth/B^2) (w/(P t).length j)
      (div_pos hw ((P t).length_pos j)) (hzero t ht j)
    exact (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hw.le ((P t).length_pos j) (hlength t ht j))
      (by positivity)).trans hj
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
    (alt t) (hAlt t) (T t) Kw hKw (hgeom t htt) (cutoff t) v hv test htest htest1
    g w B hw hB0 (hzero t htt) start l u hlu hactive sR (g.center start cell) b A
    maskExponent (Cfreq/w) z (by positivity) hf hbx hby (hconc t htt l u hlu hu)).2
  have hbudget := g.source_packet_motion_coefficient (T t) hw hB hL hA hCfreq le_rfl
    (hwidth t htt) h start sR b (hs t ht).symm hblock hel hb p maskExponent (D:ℝ)
  rw [hcell] at hbudget
  rw [hPfreq t htt] at hm
  exact hm.trans (mul_le_mul_of_nonneg_right hbudget (pow_nonneg ((T t).weight_pos hKw0 _ z).le 8))

end LipschitzHilbert.AngularGrid

end

end OAI
