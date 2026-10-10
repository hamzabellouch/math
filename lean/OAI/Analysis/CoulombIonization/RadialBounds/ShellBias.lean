import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SelectionNumerics

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff InnerProductSpace NNReal ENNReal

lemma shellSqrt_eq_norm {N : ℕ} (p : SmoothMultiplier spaceDirections) (x : Configuration N) :
    Real.sqrt ((oneBodySquareTotal p).value x) =
      ‖(WithLp.toLp 2 (fun i => p.value (x i)) : EuclideanSpace ℝ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [oneBodySquareTotal_value,Real.norm_eq_abs,sq_abs]

lemma shellSqrt_lipschitz {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x : Configuration N => Real.sqrt ((oneBodySquareTotal p).value x)) := by
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc p.regular (by simp)
  have hp : LipschitzWith K (fun x : Configuration N => (fun i => p.value (x i))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    apply (dist_pi_le_iff (by positivity)).2
    intro i
    exact (hK.dist_le_mul (x i) (y i)).trans
      (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) K.coe_nonneg)
  have hn := lipschitzWith_one_norm.comp ((PiLp.lipschitzWith_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin N => ℝ)).comp hp)
  refine ⟨1 * ((Fintype.card (Fin N) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * K), ?_⟩
  simpa only [Function.comp_def,←shellSqrt_eq_norm] using hn

 def shellBiasMultiplier {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) : FermionLipschitzMultiplier N where
  value := fun x => Real.sqrt ((oneBodySquareTotal p).value x)
  constant := Classical.choose (shellSqrt_lipschitz (N := N) p hc)
  lipschitz := Classical.choose_spec (shellSqrt_lipschitz (N := N) p hc)
  bound := by
    obtain ⟨C,hC⟩ := p.bound
    refine ⟨Real.sqrt (N*C^2),fun x => ?_⟩
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc
      _ = ∑ i : Fin N, p.value (x i)^2 := rfl
      _ ≤ ∑ _i : Fin N, C^2 := Finset.sum_le_sum (fun i _ => by
        have hh := pow_le_pow_left₀ (abs_nonneg (p.value (x i))) (hC (x i)) 2
        simpa only [sq_abs] using hh)
      _ = _ := by simp
  symmetric := by intro π x; rw [(oneBodySquareTotal p).symmetric]

lemma shellBias_value_sq {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (x : Configuration N) :
    (shellBiasMultiplier p hc).value x^2 = (oneBodySquareTotal p).value x := by
  change Real.sqrt ((oneBodySquareTotal p).value x)^2 = _
  apply Real.sq_sqrt
  change 0 ≤ ∑ i, p.value (x i)^2
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (p.value (x i)))

lemma shellBias_deriv_sq_le {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (x : Configuration N) (i : Fin N) (a : Fin 3) :
    (lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 ≤
      (lineDeriv ℝ p.value (x i) (spaceDirections a))^2 := by
  let S := fun x : Configuration N => (oneBodySquareTotal p).value x
  have hS (x : Configuration N) : 0 ≤ S x := by
    change 0 ≤ ∑ i, p.value (x i)^2
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd : fderiv ℝ S x (direction i a) =
      2*p.value (x i)*lineDeriv ℝ p.value (x i) (spaceDirections a) := by
    rw [←DifferentiableAt.lineDeriv_eq_fderiv ((oneBodySquareTotal p).regular.differentiable (by simp) x)]
    change lineDeriv ℝ (fun y => ∑ j : Fin N, (p.oneBody j).value y^2) x (direction i a) = _
    rw [lineDeriv_sumSquares]
    simp only [SmoothMultiplier.oneBody,oneBody_coordinate_derivative]
    simp
  change (lineDeriv ℝ (fun y => Real.sqrt (S y)) x (direction i a))^2 ≤ _
  by_cases hx : S x = 0
  · rw [CoulombObservation.lineDeriv_sqrt_of_zero hS hx,zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · have hp : 0 < S x := (hS x).lt_of_ne' hx
    rw [CoulombObservation.lineDeriv_sqrt_of_pos ((oneBodySquareTotal p).regular.differentiable (by simp) x) hp,hd]
    have hi : p.value (x i)^2 ≤ S x := by
      change p.value (x i)^2 ≤ ∑ j : Fin N, p.value (x j)^2
      exact Finset.single_le_sum (fun j _ => sq_nonneg (p.value (x j))) (Finset.mem_univ i)
    have hs := Real.sq_sqrt (hS x)
    have hpos := Real.sqrt_pos.2 hp
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : 0 < (2*Real.sqrt (S x))^2)).2
    simp only [mul_pow,hs]
    nlinarith only [mul_le_mul_of_nonneg_right hi (sq_nonneg (lineDeriv ℝ p.value (x i) (spaceDirections a)))]

end
open MeasureTheory Set Filter
open scoped ContDiff

lemma radialInside_abs_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) :
    |(radialInside y ht hb).value x| ≤ 1 := Real.abs_cos_le_one _
lemma radialOutside_abs_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) :
    |(radialOutside y ht hb).value x| ≤ 1 := Real.abs_sin_le_one _
lemma radialInside_deriv_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (radialInside y ht hb).value x (spaceDirections a)| ≤ Real.pi*smoothTransitionBound/b := by
  change |lineDeriv ℝ (fun z => Real.cos (radialPhase y t b z)) x (spaceDirections a)| ≤ _
  rw [radial_cos_derivative,abs_mul,abs_neg]
  exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)
lemma radialOutside_deriv_le (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (x : Space) (a : Fin 3) :
    |lineDeriv ℝ (radialOutside y ht hb).value x (spaceDirections a)| ≤ Real.pi*smoothTransitionBound/b := by
  change |lineDeriv ℝ (fun z => Real.sin (radialPhase y t b z)) x (spaceDirections a)| ≤ _
  rw [radial_sin_derivative,abs_mul]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using radialPhase_derivative_le y ht hb x a)

 def shellCutoff {u : ℝ} (hu : 0 < u) : SmoothMultiplier spaceDirections where
  value := fun x => (radialOutside 0 hu.le hu).value x *
    (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x
  regular := (radialOutside 0 hu.le hu).regular.mul (radialInside 0 (by positivity) (by positivity)).regular
  bound := ⟨1,fun x => by
    rw [abs_mul]
    exact (mul_le_mul (radialOutside_abs_le _ _ _ _) (radialInside_abs_le _ _ _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)⟩
  gradient_bound := by
    intro a
    refine ⟨Real.pi*smoothTransitionBound/u+Real.pi*smoothTransitionBound/(2*u),fun x => ?_⟩
    rw [smooth_lineDeriv_mul (radialOutside 0 hu.le hu).regular
      (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).regular]
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left (radialInside_abs_le _ _ _ _) (abs_nonneg _)).trans
        (by simpa only [mul_one] using radialOutside_deriv_le 0 hu.le hu x a)
    · exact (mul_le_mul_of_nonneg_right (radialOutside_abs_le _ _ _ _) (abs_nonneg _)).trans
        (by simpa only [one_mul] using radialInside_deriv_le 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) x a)

lemma shellCutoff_support {u : ℝ} (hu : 0 < u) (x : Space)
    (hx : (shellCutoff hu).value x ≠ 0) : u ≤ ‖x‖ ∧ ‖x‖ ≤ 4*u := by
  constructor
  · by_contra h
    have hh := (radialCut_inner hu.le hu (y := 0) (x := x) (by simpa using (le_of_lt (lt_of_not_ge h)))).2
    apply hx
    change (radialOutside 0 hu.le hu).value x*_ = 0
    change (radialOutside 0 hu.le hu).value x = 0 at hh
    rw [hh,zero_mul]
  · by_contra h
    have hh := (radialCut_outer (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) (y := 0) (x := x) (by simp only [sub_zero]; linarith)).1
    apply hx
    change _*(radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x = 0
    change (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x = 0 at hh
    rw [hh,mul_zero]

lemma shellCutoff_compact {u : ℝ} (hu : 0 < u) : HasCompactSupport (shellCutoff hu).value := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (4*u))
  intro x hx
  by_contra hh
  exact hx (by simpa only [Metric.mem_closedBall,dist_zero_right] using (shellCutoff_support hu x hh).2)

lemma shellCutoff_partition {u : ℝ} (hu : 0 < u) (x : Space) :
    (shellCutoff hu).value x^2 =
      (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x^2 -
        (radialInside 0 hu.le hu).value x^2 := by
  have hsum := radialCut_partition 0 hu.le hu x
  simp only [Fin.sum_univ_two,radialCut,Matrix.cons_val_zero,Matrix.cons_val_one] at hsum
  by_cases hx : ‖x‖ ≤ 2*u
  · have hh := (radialCut_inner (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u) (y := 0) (x := x) (by simpa using hx)).1
    change (radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x = 1 at hh
    change ((radialOutside 0 hu.le hu).value x*(radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x)^2 = _
    rw [hh,mul_one]
    linarith only [hsum]
  · have hh := radialCut_outer hu.le hu (y := 0) (x := x) (by simp only [sub_zero]; linarith [lt_of_not_ge hx])
    change (radialInside 0 hu.le hu).value x = 0 ∧ (radialOutside 0 hu.le hu).value x = 1 at hh
    change ((radialOutside 0 hu.le hu).value x*(radialInside 0 (by positivity : 0 ≤ 2*u) (by positivity : 0 < 2*u)).value x)^2 = _
    rw [hh.1,hh.2,one_mul,zero_pow (by decide : 2 ≠ 0),sub_zero]

end CoulombAtom

end

end OAI
