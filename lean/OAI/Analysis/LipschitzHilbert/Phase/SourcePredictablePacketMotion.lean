import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskMotion
import OAI.Analysis.LipschitzHilbert.Estimates.CarrierSlopeMotion
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictableLength

namespace OAI

/-! Predictable-length motion of the actual masked physical packet
intervals, expressed in the carrier common to one angular child. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
open PhaseCombinatorics

theorem source_predictable_masked_interval_motion (p : ℝ) (D Bslots : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ Bslots), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceLabeledTopGeometry P T K D →
      ∀ (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (test : ℝ × ℝ → EuclideanSpace ℂ κ),
        Measurable test → (∀ z, ‖test z‖ ≤ 1) →
      ∀ (grid : AngularGrid) (w Bscale : ℝ) (hw : 0 < w), 0 < Bscale →
      (∀ j, grid.eligible (grid.rootWidth/Bscale^2) (w/P.length j) 0) →
      ∀ (start lower upper : ℕ), lower ≤ upper →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper →
        start ≤ grid.lastEligible (grid.rootWidth/Bscale^2) (w/P.length j)
          (div_pos hw (P.length_pos j))) →
      ∀ (sR center b A maskExponent Fbound : ℝ) (z : ℝ × ℝ),
      0 ≤ Fbound → (∀ k, |P.frequency k| ≤ Fbound) →
      |b| ≤ T.length → |(sR-T.slope)*b| ≤ T.width →
      let coeff := P.physicalCoefficient T.slope cutoff v test
      let Q := P.withProfile alt hAlt
      let F := Q.rawInterval coeff 0 lower upper
      let S := fun zz : ℝ × ℝ => Q.rawInterval
        (fun j l u => T.mask L maskExponent zz • coeff j l u) 0 lower upper
        zz.1 (zz.2-T.slope*zz.1)
      let h₀ := T.weight K (D:ℝ) z
      let r := Bscale^2*w/grid.width start
      (∀ y, |y-(z.2-T.slope*z.1)| ≤ T.width →
        ‖F z.1 y‖+T.width*‖covariantSignal P.frequency (fun k t => F z.1 t k) y‖ ≤ A*h₀^8) →
      ‖S z‖ ≤ A*h₀^8 ∧
      ‖S (SlopeBox.lineShift sR b z)-
        diagonalModulation P.frequency (S z) ((sR-center)*b)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|b|+(A/T.width)*|(sR-T.slope)*b|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|b|/T.length+|(sR-T.slope)*b|/T.width)*A+
        Fbound*A*|T.slope-center| * |b|)*h₀^8 := by
  obtain ⟨L0,hL0,hB,hmotion⟩ := source_labeled_masked_interval_motion p D Bslots
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK hgeom
    cutoff v hv test htest htest1 grid w Bscale hw hBscale hzero start lower upper hlu
    hactive sR center b A maskExponent Fbound z hFbound hfreq hbx hby
  dsimp only
  intro hc
  let coeff := P.physicalCoefficient T.slope cutoff v test
  let Q := P.withProfile alt hAlt
  let F := Q.rawInterval coeff 0 lower upper
  let S := fun zz : ℝ × ℝ => Q.rawInterval
    (fun j l u => T.mask L maskExponent zz • coeff j l u) 0 lower upper
    zz.1 (zz.2-T.slope*zz.1)
  let h₀ := T.weight K (D:ℝ) z
  let r := Bscale^2*w/grid.width start
  let y₀ := z.2-T.slope*z.1
  let y₁ := (SlopeBox.lineShift sR b z).2-T.slope*(SlopeBox.lineShift sR b z).1
  have hr : 0 < r := div_pos (mul_pos (sq_pos_of_pos hBscale) hw) (grid.width_pos start)
  have hlength (j : Fin N) (hjl : lower ≤ j.val) (hju : j.val < upper) : r ≤ P.length j :=
    P.source_stopping_length_lower grid hw hBscale hzero start j (hactive j hjl hju)
  have hxy₀ : (z.1,y₀+T.slope*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp [y₀]
      ring
  have hxy₁ : ((SlopeBox.lineShift sR b z).1,
      y₁+T.slope*(SlopeBox.lineShift sR b z).1) = SlopeBox.lineShift sR b z := by
    apply Prod.ext
    · rfl
    · dsimp [y₁]
      ring
  have hx : (SlopeBox.lineShift sR b z).1-z.1 = b := by simp [SlopeBox.lineShift]
  have hy : y₁-y₀ = (sR-T.slope)*b := by dsimp [y₁,y₀,SlopeBox.lineShift]; ring
  have hc' : ∀ y, |y-y₀| ≤ T.width →
      ‖F z.1 y‖+T.width*‖covariantSignal P.frequency (fun k t => F z.1 t k) y‖ ≤
        A*(T.weight K (D:ℝ) (z.1,y₀+T.slope*z.1))^8 := by
    simpa only [hxy₀] using hc
  have hm := hmotion L hLL N κ Label Item P hcard hP alt hAlt T K hK hgeom
    cutoff v hv test htest htest1 lower upper hlu r hr hlength
    z.1 (SlopeBox.lineShift sR b z).1 y₀ y₁ A maskExponent
    (by simpa only [hx] using hbx) (by simpa only [hy] using hby) hc'
  have hS (zz : ℝ × ℝ) : S zz = T.mask L maskExponent zz • F zz.1 (zz.2-T.slope*zz.1) :=
    Q.rawInterval_coeff_smul coeff (T.mask L maskExponent zz) 0 lower upper _ _
  have hbase : ‖F z.1 y₀‖ ≤ A*h₀^8 := by
    have h := hc y₀ (by simp [y₀,T.width_pos.le])
    have hnonneg := mul_nonneg T.width_pos.le
      (norm_nonneg (covariantSignal P.frequency (fun k t => F z.1 t k) y₀))
    change ‖F z.1 y₀‖+_ ≤ A*h₀^8 at h
    linarith
  have hmask : |T.mask L maskExponent z| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hSbase : ‖S z‖ ≤ A*h₀^8 := by
    rw [hS, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hmask (norm_nonneg _)).trans
      (by simpa only [one_mul] using hbase)
  have htop : ‖S (SlopeBox.lineShift sR b z)-
      diagonalModulation P.frequency (S z) ((sR-T.slope)*b)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|b|+(A/T.width)*|(sR-T.slope)*b|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|b|/T.length+|(sR-T.slope)*b|/T.width)*A)*h₀^8 := by
    rw [hS, hS]
    simpa only [hx,hy,hxy₀,hxy₁] using hm
  refine ⟨hSbase,?_⟩
  have h := carrier_replacement_motion P.frequency (S z) (S (SlopeBox.lineShift sR b z))
    Fbound (A*h₀^8)
    (((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|b|+(A/T.width)*|(sR-T.slope)*b|+
      (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
        (|b|/T.length+|(sR-T.slope)*b|/T.width)*A)*h₀^8)
    hFbound hfreq hSbase sR T.slope center b htop
  convert h using 1
  ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
