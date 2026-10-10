import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorDerivative
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictablePacketMotion

namespace OAI

/-! Carrier and top-mask motion for the original smooth-selector
coefficients. The snapshot concentration premise remains the original
one; the horizontal derivative is proved from the original packets. -/

noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert.SourceLabeledLattice
open PhaseCombinatorics

theorem source_selector_interval_motion (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ x0 x1 y0 y1 A : ℝ, |x1-x0| ≤ T.length → |y1-y0| ≤ T.width →
      let F := (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient T.slope selector v g) 0 lower upper
      (∀ y, |y-y0| ≤ T.width → ‖F x0 y‖ + T.width *
        ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤
          A*(T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8) →
      ‖F x1 y1 - diagonalModulation P.frequency (F x0 y0) (y1-y0)‖ ≤
        ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x1-x0| +
          (A/T.width)*|y1-y0|) * (T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8 := by
  obtain ⟨L0,hL0,hB,hderiv⟩ := source_selector_top_derivative p D B
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G selector hselector hselector1 v hv g hg hg1
    lower upper hlu r hr hs x0 x1 y0 y1 A hx hy
  dsimp only
  intro hconcentration
  let Q := P.withProfile alt hAlt
  let coeff := P.physicalMultiplierCoefficient T.slope selector v g
  let F := Q.rawInterval coeff 0 lower upper
  let w0 := (T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hLp : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hDx (x : ℝ) (hxx : x ∈ uIcc x0 x1) :
      ‖deriv (fun t => F t y1) x‖ ≤ (L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*w0 := by
    have hxlocal : |x-x0| ≤ T.length := (abs_sub_left_of_mem_uIcc hxx).trans hx
    have hw := T.weight_slope_coordinates_local hK (Nat.cast_nonneg D) hxlocal hy
    have hw8 := pow_le_pow_left₀ (T.weight_pos hK0 (D:ℝ) _).le hw 8
    have hexp : (Real.exp (2*(D:ℝ)))^8 = Real.exp (16*(D:ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow, hexp] at hw8
    have hd := hderiv L hLL N κ Label Item P hcard hP alt hAlt T K hK0 G
      selector hselector hselector1 v hv g hg hg1 lower upper hlu r hr hs (x, y1+T.slope*x)
    have heq : y1+T.slope*x-T.slope*x = y1 := by ring
    simp only [heq] at hd
    change ‖deriv (fun t => F t y1) x‖ ≤ _ at hd
    exact hd.trans (by
      convert mul_le_mul_of_nonneg_left hw8 (div_nonneg (Real.rpow_nonneg hLp.le _) hr.le) using 1
      ring)
  have hDy (y : ℝ) (hyy : y ∈ uIcc y0 y1) :
      ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤ (A/T.width)*w0 := by
    have h := hconcentration y ((abs_sub_left_of_mem_uIcc hyy).trans hy)
    have hb : T.width * ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤ A*w0 := by
      change ‖F x0 y‖ + _ ≤ _ at h
      linarith [norm_nonneg (F x0 y)]
    calc
      _ ≤ (A*w0)/T.width := (le_div_iff₀ T.width_pos).mpr (by simpa only [mul_comm] using hb)
      _ = _ := by ring
  have h := covariant_line_motion F P.frequency x0 x1 y0 y1
    ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*w0) ((A/T.width)*w0)
    (fun x _ => Q.rawInterval_horizontal_differentiable coeff 0 lower upper hlu x y1)
    (fun y _ k => Q.rawInterval_vertical_differentiable coeff 0 lower upper x0 y k)
    hDx hDy
  convert h using 1
  dsimp only [w0]
  ring


theorem source_selector_masked_interval_motion (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ x₀ x₁ y₀ y₁ A maskExponent : ℝ,
      |x₁-x₀| ≤ T.length → |y₁-y₀| ≤ T.width →
      let F := (P.withProfile alt hAlt).rawInterval
        (P.physicalMultiplierCoefficient T.slope selector v g) 0 lower upper
      let w₀ := (T.weight K (D:ℝ) (x₀,y₀+T.slope*x₀))^8
      (∀ y, |y-y₀| ≤ T.width → ‖F x₀ y‖+T.width*
        ‖covariantSignal P.frequency (fun k t => F x₀ t k) y‖ ≤ A*w₀) →
      ‖T.mask L maskExponent (x₁,y₁+T.slope*x₁) • F x₁ y₁-
        diagonalModulation P.frequency
          (T.mask L maskExponent (x₀,y₀+T.slope*x₀) • F x₀ y₀) (y₁-y₀)‖ ≤
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*
          (|x₁-x₀|/T.length+|y₁-y₀|/T.width)*A)*w₀ := by
  obtain ⟨L0,hL0,hB,hmotion⟩ := source_selector_interval_motion p D B
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G selector hselector hselector1 v hv g hg hg1
    lower upper hlu r hr hs x₀ x₁ y₀ y₁ A maskExponent hx hy
  dsimp only
  intro hc
  let F := (P.withProfile alt hAlt).rawInterval
    (P.physicalMultiplierCoefficient T.slope selector v g) 0 lower upper
  let w₀ := (T.weight K (D:ℝ) (x₀,y₀+T.slope*x₀))^8
  have hL : 0 < L := zero_lt_one.trans_le (hL0.trans hLL)
  have hm := hmotion L hLL N κ Label Item P hcard hP alt hAlt T K hK G
    selector hselector hselector1 v hv g hg hg1 lower upper hlu r hr hs x₀ x₁ y₀ y₁ A hx hy hc
  have hbase : ‖F x₀ y₀‖ ≤ A*w₀ := by
    have hb := hc y₀ (by simp [T.width_pos.le])
    have hn := mul_nonneg T.width_pos.le
      (norm_nonneg (covariantSignal P.frequency (fun k t => F x₀ t k) y₀))
    change ‖F x₀ y₀‖+_ ≤ A*w₀ at hb
    linarith
  have hq : |T.mask L maskExponent (x₁,y₁+T.slope*x₁)| ≤ 1 := by
    change |topSincMask L maskExponent _ _| ≤ 1
    rw [abs_of_nonneg (topSincMask_nonneg _ _ _ _)]
    exact topSincMask_le_one _ _ _ _
  have hlength := T.length_pos
  have hwidth := T.width_pos
  have h := masked_isometry_motion
    (diagonalModulationRealIsometry P.frequency (y₁-y₀))
    (F x₁ y₁) (F x₀ y₀)
    (T.mask L maskExponent (x₁,y₁+T.slope*x₁))
    (T.mask L maskExponent (x₀,y₀+T.slope*x₀)) (A*w₀)
    (((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|)*w₀)
    ((2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width))
    hq (by positivity) (T.mask_slope_coordinates_motion L maskExponent x₀ x₁ y₀ y₁ hL)
    hbase hm
  have heq :
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|)*w₀+
        ((2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width))*(A*w₀) =
      ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x₁-x₀|+(A/T.width)*|y₁-y₀|+
        (2*(⌈L⌉₊:ℝ)/L^maskExponent)*(|x₁-x₀|/T.length+|y₁-y₀|/T.width)*A)*w₀ := by
    ring
  rw [heq] at h
  simpa only [diagonalModulationRealIsometry_apply] using h


theorem source_selector_predictable_masked_interval_motion (p : ℝ) (D Bslots : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (Bslots : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ Bslots), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceLabeledTopGeometry P T K D →
      ∀ (selector : ∀ j, P.labels j → κ → ℝ → ℂ),
        (∀ j l k, Measurable (selector j l k)) →
        (∀ j l k s, ‖selector j l k s‖ ≤ 1) →
      ∀ (v : ℝ × ℝ → ℝ), Measurable v →
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
      let coeff := P.physicalMultiplierCoefficient T.slope selector v test
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
  obtain ⟨L0,hL0,hB,hmotion⟩ := source_selector_masked_interval_motion p D Bslots
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK hgeom
    selector hselector hselector1 v hv test htest htest1 grid w Bscale hw hBscale hzero start lower upper hlu
    hactive sR center b A maskExponent Fbound z hFbound hfreq hbx hby
  dsimp only
  intro hc
  let coeff := P.physicalMultiplierCoefficient T.slope selector v test
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
    selector hselector hselector1 v hv test htest htest1 lower upper hlu r hr hlength
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
