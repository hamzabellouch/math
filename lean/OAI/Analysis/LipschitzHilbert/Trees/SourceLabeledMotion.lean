import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledDerivative
import OAI.Analysis.LipschitzHilbert.Fourier.CovariantLineMotion
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketContinuity

namespace OAI

/-! Local motion of the actual labeled interval sums after removing the
common vertical carrier. The concentration estimate is used only on the
vertical segment through the initial point; horizontal derivatives are
unconditional. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert
open PhaseCombinatorics

namespace SlopeBox

/-- Comparing the two normalized coordinates controls the actual top
weight, including away from the significant region. -/
theorem weight_slope_coordinates_le (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (x0 x1 y0 y1 : ℝ) :
    T.weight K D (x1, y1 + T.slope*x1) ≤
      Real.exp ((D/K) * (|x1-x0|/T.length + |y1-y0|/T.width)) *
        T.weight K D (x0, y0 + T.slope*x0) := by
  let z0 := (x0, y0 + T.slope*x0)
  let z1 := (x1, y1 + T.slope*x1)
  have hx : T.horizontal z1 - T.horizontal z0 = (x1-x0)/T.length := by
    dsimp [horizontal, z0, z1]
    ring
  have hy : T.transverse z1 - T.transverse z0 = (y1-y0)/T.width := by
    dsimp [transverse, z0, z1]
    ring
  have hr : |T.radius z1 - T.radius z0| ≤ |x1-x0|/T.length + |y1-y0|/T.width := by
    calc
      _ = |(|T.horizontal z1|-|T.horizontal z0|) +
          (|T.transverse z1|-|T.transverse z0|)| := by unfold radius; congr 1; ring
      _ ≤ |(|T.horizontal z1|-|T.horizontal z0|)| +
          |(|T.transverse z1|-|T.transverse z0|)| := abs_add_le _ _
      _ ≤ |T.horizontal z1-T.horizontal z0| + |T.transverse z1-T.transverse z0| :=
        add_le_add (abs_abs_sub_abs_le_abs_sub _ _) (abs_abs_sub_abs_le_abs_sub _ _)
      _ = _ := by rw [hx, hy, abs_div, abs_div, abs_of_pos T.length_pos, abs_of_pos T.width_pos]
  have hb (z : ℝ × ℝ) : 1 ≤ 1 + T.radius z/K := by
    exact le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative z) hK.le)
  have hl := log_motion_of_lower_bound (by norm_num : (0:ℝ)<1) (hb z1) (hb z0)
  have heq : (1+T.radius z1/K)-(1+T.radius z0/K) = (T.radius z1-T.radius z0)/K := by ring
  rw [div_one, heq, abs_div, abs_of_pos hK] at hl
  have hlog : |Real.log (T.weight K D z1)-Real.log (T.weight K D z0)| ≤
      (D/K) * (|x1-x0|/T.length + |y1-y0|/T.width) := by
    rw [T.log_weight hK, T.log_weight hK]
    calc
      _ = D * |Real.log (1+T.radius z1/K)-Real.log (1+T.radius z0/K)| := by
        rw [show D*Real.log 2-D*Real.log (1+T.radius z1/K) -
          (D*Real.log 2-D*Real.log (1+T.radius z0/K)) =
          -(D*(Real.log (1+T.radius z1/K)-Real.log (1+T.radius z0/K))) by ring,
          abs_neg, abs_mul, abs_of_nonneg hD]
      _ ≤ D * (|T.radius z1-T.radius z0|/K) := mul_le_mul_of_nonneg_left hl hD
      _ ≤ D * ((|x1-x0|/T.length + |y1-y0|/T.width)/K) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr hK.le) hD
      _ = _ := by ring
  calc
    _ = Real.exp (Real.log (T.weight K D z1)) := (Real.exp_log (T.weight_pos hK D z1)).symm
    _ ≤ Real.exp ((D/K)*(|x1-x0|/T.length + |y1-y0|/T.width) +
        Real.log (T.weight K D z0)) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hlog).2])
    _ = _ := by rw [Real.exp_add, Real.exp_log (T.weight_pos hK D z0)]

/-- Motion through one top length and width costs only a fixed factor. -/
theorem weight_slope_coordinates_local (T : SlopeBox) {K D : ℝ}
    (hK : 1 ≤ K) (hD : 0 ≤ D) {x0 x1 y0 y1 : ℝ}
    (hx : |x1-x0| ≤ T.length) (hy : |y1-y0| ≤ T.width) :
    T.weight K D (x1, y1 + T.slope*x1) ≤
      Real.exp (2*D) * T.weight K D (x0, y0 + T.slope*x0) := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  apply (T.weight_slope_coordinates_le hK0 hD x0 x1 y0 y1).trans
  apply mul_le_mul_of_nonneg_right _ (T.weight_pos hK0 D _).le
  apply Real.exp_le_exp.mpr
  have hx' : |x1-x0|/T.length ≤ 1 := (div_le_one T.length_pos).mpr hx
  have hy' : |y1-y0|/T.width ≤ 1 := (div_le_one T.width_pos).mpr hy
  calc
    _ ≤ (D/K)*2 := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hD hK0.le)
    _ ≤ D*2 := mul_le_mul_of_nonneg_right (div_le_self hD hK) (by norm_num)
    _ = _ := by ring

end SlopeBox

namespace SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawInterval_horizontal_differentiable
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (hlu : lower ≤ upper) (x y : ℝ) :
    DifferentiableAt ℝ (fun x => P.rawInterval coeff i lower upper x y) x := by
  exact planarPacketInterval_horizontal_differentiable_schwartz
    (ι := fun j => Σ l : P.labels j, Item j l) (fun j p => coeff j p.1 p.2)
    (fun j p k t => P.raw i j p.1 p.2 k t) lower upper hlu x y

theorem rawInterval_vertical_differentiable
    (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (i : Fin 3) (lower upper : ℕ) (x y : ℝ) (k : κ) :
    DifferentiableAt ℝ (fun y => P.rawInterval coeff i lower upper x y k) y := by
  apply planarPacketInterval_component_differentiable
    (ι := fun j => Σ l : P.labels j, Item j l)
  intro j p
  exact modulatedPlanarJet_differentiable (P.profile j p.1 p.2 k)
    (P.actualX j p.1 p.2) (P.actualZ j p.1 p.2) (P.length j) P.width
    (-P.rowSlope j p.1) (P.frequency k) P.scale y (P.length_pos j).ne' i x

/-- The established interval concentration at the initial point, together
with the unconditional derivative bound, gives carrier-free local motion
for the original physical analyzing coefficients. -/
theorem source_labeled_interval_motion (p : ℝ) (D B : ℕ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ (B : ℝ) ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
        [Fintype κ] [∀ j l, Fintype (Item j l)]
        (P : SourceLabeledLattice N κ Label Item)
        (_hcard : ∀ j, (P.labels j).card ≤ B), P.constant ≤ L^p →
      ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
        (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
        (T : SlopeBox) (K : ℝ), 1 ≤ K → SourceLabeledTopGeometry P T K D →
      ∀ (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ), Measurable v →
      ∀ (g : ℝ × ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      ∀ (lower upper : ℕ), lower ≤ upper → ∀ r : ℝ, 0 < r →
      (∀ j : Fin N, lower ≤ j.val → j.val < upper → r ≤ P.length j) →
      ∀ x0 x1 y0 y1 A : ℝ, |x1-x0| ≤ T.length → |y1-y0| ≤ T.width →
      let F := (P.withProfile alt hAlt).rawInterval
        (P.physicalCoefficient T.slope cutoff v g) 0 lower upper
      (∀ y, |y-y0| ≤ T.width → ‖F x0 y‖ + T.width *
        ‖covariantSignal P.frequency (fun k t => F x0 t k) y‖ ≤
          A*(T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8) →
      ‖F x1 y1 - diagonalModulation P.frequency (F x0 y0) (y1-y0)‖ ≤
        ((L^(2*p+4)/r)*Real.exp (16*(D:ℝ))*|x1-x0| +
          (A/T.width)*|y1-y0|) * (T.weight K (D:ℝ) (x0, y0+T.slope*x0))^8 := by
  obtain ⟨L0,hL0,hB,hderiv⟩ := source_labeled_top_derivative p D B
  refine ⟨L0,hL0,hB,?_⟩
  intro L hLL N κ Label Item _ _ P hcard hP alt hAlt T K hK G cutoff v hv g hg hg1
    lower upper hlu r hr hs x0 x1 y0 y1 A hx hy
  dsimp only
  intro hconcentration
  let Q := P.withProfile alt hAlt
  let coeff := P.physicalCoefficient T.slope cutoff v g
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
      cutoff v hv g hg hg1 lower upper hlu r hr hs (x, y1+T.slope*x)
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

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
