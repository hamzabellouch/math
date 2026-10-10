import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusFourierTranslation
import OAI.Analysis.Conductivity.Geometry.TorusExponential
import OAI.Analysis.Conductivity.Sources.WeightedSpectralSpace

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torus_lipschitz_H1_summable (f : C(UnitAddTorus (Fin 2),ℂ))
    (K : ℝ≥0) (hf : LipschitzWith K f) :
    Summable (fun h : Fin 2 → ℤ =>
      (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*‖mFourierCoeff f h‖^2) := by
  have h0 : Summable (fun h : Fin 2 → ℤ => ‖mFourierCoeff f h‖^2) := by
    simpa only [mFourierCoeff_toLp] using
      (hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 volume ℂ f)).summable
  have hj (j : Fin 2) : Summable (fun h : Fin 2 → ℤ => (h j:ℝ)^2*‖mFourierCoeff f h‖^2) := by
    have hh := (torus_coordinate_fourier_summable f j K K.coe_nonneg
      (torus_lipschitz_coordinate_bound f K hf j)).mul_left ((2*Real.pi)^2)⁻¹
    apply hh.congr
    intro h
    have hp : Real.pi≠0 := Real.pi_pos.ne'
    field_simp
  apply ((h0.add (hj 0)).add (hj 1)).congr
  intro h
  ring

lemma torus_coordinate_H1_summable (f : C(UnitAddTorus (Fin 2),ℂ))
    (K : Fin 2 → ℝ) (hK : ∀ j,0≤K j)
    (hf : ∀ j t x,‖f (x+torusCoordinateShift j t)-f x‖≤K j*|t|) :
    Summable (fun h : Fin 2 → ℤ =>
      (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*‖mFourierCoeff f h‖^2) := by
  have h0 : Summable (fun h : Fin 2 → ℤ => ‖mFourierCoeff f h‖^2) := by
    simpa only [mFourierCoeff_toLp] using
      (hasSum_sq_mFourierCoeff (ContinuousMap.toLp 2 volume ℂ f)).summable
  have hj (j : Fin 2) : Summable (fun h : Fin 2 → ℤ => (h j:ℝ)^2*‖mFourierCoeff f h‖^2) := by
    have hh := (torus_coordinate_fourier_summable f j (K j) (hK j) (hf j)).mul_left ((2*Real.pi)^2)⁻¹
    apply hh.congr
    intro h
    have hp : Real.pi≠0 := Real.pi_pos.ne'
    field_simp
  apply ((h0.add (hj 0)).add (hj 1)).congr
  intro h
  ring

lemma torusRate_polynomial_bound (s : Fin 3 → ℝ) (h : Fin 2 → ℤ) :
    torusRate s h≤(1+|s 0|+|s 1|+|s 2|)*(1+(h 0:ℝ)^2+(h 1:ℝ)^2) := by
  let C := 1+|s 0|+|s 1|+|s 2|
  let B := (h 0:ℝ)^2+(h 1:ℝ)^2
  have hC : 1≤C := by dsimp [C]; linarith [abs_nonneg (s 0),abs_nonneg (s 1),abs_nonneg (s 2)]
  have hB : 0≤B := by dsimp [B]; positivity
  have hcross : 2*s 1*(h 0:ℝ)*(h 1:ℝ)≤|s 1| * B := by
    have hab : 2*|(h 0:ℝ)| * |(h 1:ℝ)| ≤ B := by
      dsimp [B]
      nlinarith [sq_nonneg (|(h 0:ℝ)|-|(h 1:ℝ)|),sq_abs (h 0:ℝ),sq_abs (h 1:ℝ)]
    calc
      _≤|2*s 1*(h 0:ℝ)*(h 1:ℝ)| := le_abs_self _
      _=|s 1| * (2*|(h 0:ℝ)| * |(h 1:ℝ)|) := by rw [abs_mul,abs_mul,abs_mul]; norm_num; ring
      _≤|s 1| * B := mul_le_mul_of_nonneg_left hab (abs_nonneg _)
  have hQ : torusQuadratic s h≤C*B := by
    have hx := mul_le_mul_of_nonneg_right (le_abs_self (s 0)) (sq_nonneg (h 0:ℝ))
    have hy := mul_le_mul_of_nonneg_right (le_abs_self (s 2)) (sq_nonneg (h 1:ℝ))
    have hx' : |s 0| * (h 0:ℝ)^2≤|s 0| * B := mul_le_mul_of_nonneg_left
      (by dsimp [B]; nlinarith [sq_nonneg (h 1:ℝ)]) (abs_nonneg _)
    have hy' : |s 2| * (h 1:ℝ)^2≤|s 2| * B := mul_le_mul_of_nonneg_left
      (by dsimp [B]; nlinarith [sq_nonneg (h 0:ℝ)]) (abs_nonneg _)
    dsimp [torusQuadratic,C]
    nlinarith
  have hroot : torusRate s h≤1+max (torusQuadratic s h) 0 := by
    dsimp [torusRate]
    by_cases hq : 0≤torusQuadratic s h
    · rw [max_eq_left hq]
      have hh := Real.sq_sqrt hq
      nlinarith [sq_nonneg (Real.sqrt (torusQuadratic s h)-1)]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hq),max_eq_right (le_of_not_ge hq)]
      norm_num
  have hm : max (torusQuadratic s h) 0≤C*B := max_le hQ (mul_nonneg (by linarith) hB)
  change torusRate s h≤C*(1+(h 0:ℝ)^2+(h 1:ℝ)^2)
  calc
    _≤1+C*B := hroot.trans (add_le_add (le_refl 1) hm)
    _≤C*(1+(h 0:ℝ)^2+(h 1:ℝ)^2) := by dsimp [B] at *; nlinarith

theorem torus_lipschitz_trace_summable (s : Fin 3 → ℝ)
    (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0) (hf : LipschitzWith K f) :
    Summable (fun h : Fin 2 → ℤ => torusRate s h*‖mFourierCoeff f h‖^2) := by
  refine ((torus_lipschitz_H1_summable f K hf).mul_left (1+|s 0|+|s 1|+|s 2|)).of_nonneg_of_le
    (fun h => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (fun h => ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (torusRate_polynomial_bound s h) (sq_nonneg _)

theorem torus_coordinate_trace_summable (s : Fin 3 → ℝ)
    (f : C(UnitAddTorus (Fin 2),ℂ)) (K : Fin 2 → ℝ) (hK : ∀ j,0≤K j)
    (hf : ∀ j t x,‖f (x+torusCoordinateShift j t)-f x‖≤K j*|t|) :
    Summable (fun h : Fin 2 → ℤ => torusRate s h*‖mFourierCoeff f h‖^2) := by
  refine ((torus_coordinate_H1_summable f K hK hf).mul_left (1+|s 0|+|s 1|+|s 2|)).of_nonneg_of_le
    (fun h => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (fun h => ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (torusRate_polynomial_bound s h) (sq_nonneg _)

theorem torus_lipschitz_trace_exists (s : Fin 3 → ℝ)
    (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0) (hf : LipschitzWith K f) :
    ∃ z : spectralTraceGraph (torusRate s), ∀ h,(z.val 0) h=mFourierCoeff f h := by
  let F := (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ f)
  have he h : F h=mFourierCoeff f h := by rw [mFourierBasis_repr,mFourierCoeff_toLp]
  obtain ⟨z,hz⟩ := (spectralTraceGraph_exists_iff (fun _ => Real.sqrt_nonneg _) F).mpr
    (by simpa only [he,torusRate] using torus_lipschitz_trace_summable s f K hf)
  exact ⟨z,fun h => by rw [hz,he]⟩

end ScalarConductivity

end

end OAI
