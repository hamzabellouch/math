import Mathlib
import OAI.Computability.QuantumFactoring.OrderTrial

namespace OAI

section

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial MeasureTheory intervalIntegral

lemma residueIntegral_eq_primitive {d : ℕ} (hd : 0 < d) {u η : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ d) (hη : |η| ≤ 1/2) (hη₀ : η ≠ 0) :
    residueIntegral d u η = (d:ℂ)⁻¹*(η:ℂ)⁻¹*(spline (u/d+η)-spline (u/d)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha₀ : 0 ≤ u/d := div_nonneg hu₀ hd'.le
  have ha₁ : u/d ≤ 1 := (div_le_one hd').mpr hu₁
  obtain ⟨hηl,hηu⟩ := abs_le.mp hη
  unfold residueIntegral averagePhase
  rw [integral_comp_add_mul phase hη₀, mul_zero, add_zero, mul_one,
    spline_integral (by linarith) (by linarith) (by linarith) (by linarith),
    Complex.real_smul, Complex.ofReal_inv, mul_assoc]

lemma residueIntegral_zero (d : ℕ) (u : ℝ) :
    residueIntegral d u 0 = (d:ℂ)⁻¹*phase (u/d) := by
  simp [residueIntegral, averagePhase]

noncomputable def rampLinear (q a : ℤ) : ℚ[X] := if a ≤ q then X-C ((a:ℚ)/4) else 0

lemma evalReal_rampLinear (q a : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) :
    evalReal (rampLinear q a) x = max 0 (x-(a:ℝ)/4) := by
  by_cases h : a ≤ q
  · have h' : (a:ℝ) ≤ q := by exact_mod_cast h
    have hx : 0 ≤ x-(a:ℝ)/4 := by linarith
    simp only [rampLinear, ite_eq_left h, evalReal, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, max_eq_right hx]
    norm_num
  · have h' : (q:ℝ)+1 ≤ a := by exact_mod_cast (show q+1 ≤ a by omega)
    have hx : x-(a:ℝ)/4 ≤ 0 := by linarith
    simp [rampLinear, h, evalReal, max_eq_left hx]

noncomputable def phaseRePiece (q : ℤ) : ℚ[X] :=
  -1+C 4*(X+C (1/2))-C 8*rampLinear q 0+C 8*rampLinear q 2-C 8*rampLinear q 4
noncomputable def phaseImPiece (q : ℤ) : ℚ[X] :=
  C 4*(X+C (1/2))-C 8*rampLinear q (-1)+C 8*rampLinear q 1-
    C 8*rampLinear q 3+C 8*rampLinear q 5

lemma evalReal_phaseRePiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (phaseRePiece q) x = splineReDeriv x := by
  have h0 := evalReal_rampLinear q 0 h₀ h₁
  have h2 := evalReal_rampLinear q 2 h₀ h₁
  have h4 := evalReal_rampLinear q 4 h₀ h₁
  simp only [evalReal, phaseRePiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_neg, Polynomial.eval₂_mul, Polynomial.eval₂_one,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  change -1 + (4:ℚ)*(x+(1/2:ℚ)) - (8:ℚ)*evalReal (rampLinear q 0) x +
    (8:ℚ)*evalReal (rampLinear q 2) x - (8:ℚ)*evalReal (rampLinear q 4) x = splineReDeriv x
  rw [h0,h2,h4]
  norm_num [splineReDeriv]

lemma evalReal_phaseImPiece (q : ℤ) {x : ℝ} (h₀ : (q:ℝ)/4 ≤ x)
    (h₁ : x ≤ ((q:ℝ)+1)/4) : evalReal (phaseImPiece q) x = splineImDeriv x := by
  have hm1 := evalReal_rampLinear q (-1) h₀ h₁
  have h1 := evalReal_rampLinear q 1 h₀ h₁
  have h3 := evalReal_rampLinear q 3 h₀ h₁
  have h5 := evalReal_rampLinear q 5 h₀ h₁
  simp only [evalReal, phaseImPiece, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change (4:ℚ)*(x+(1/2:ℚ)) - (8:ℚ)*evalReal (rampLinear q (-1)) x +
    (8:ℚ)*evalReal (rampLinear q 1) x - (8:ℚ)*evalReal (rampLinear q 3) x +
    (8:ℚ)*evalReal (rampLinear q 5) x = splineImDeriv x
  rw [hm1,h1,h3,h5]
  norm_num [splineImDeriv]

lemma rampLinear_natDegree_le (q a : ℤ) : (rampLinear q a).natDegree ≤ 1 := by
  unfold rampLinear
  split_ifs
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp

lemma phaseRePiece_natDegree_le (q : ℤ) : (phaseRePiece q).natDegree ≤ 1 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  unfold phaseRePiece
  apply poly_sub_degree
  · apply poly_add_degree
    · apply poly_sub_degree
      · apply poly_add_degree
        · simp
        · exact (natDegree_C_mul_le _ _).trans hX
      · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)

lemma phaseImPiece_natDegree_le (q : ℤ) : (phaseImPiece q).natDegree ≤ 1 := by
  have hX : (X+C (1/2:ℚ)).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_add_le _ _) (by simp)
  unfold phaseImPiece
  apply poly_add_degree
  · apply poly_sub_degree
    · apply poly_add_degree
      · apply poly_sub_degree
        · exact (natDegree_C_mul_le _ _).trans hX
        · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
      · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
    · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)
  · exact (natDegree_C_mul_le _ _).trans (rampLinear_natDegree_le _ _)

end ExactQuantumFactoring.OrderTrial

namespace ExactQuantumFactoring.OrderTrial
open scoped Polynomial
open Polynomial

@[simp] lemma evalReal_add (p q : ℚ[X]) (x : ℝ) : evalReal (p+q) x = evalReal p x+evalReal q x :=
  Polynomial.eval₂_add _ _
@[simp] lemma evalReal_sub (p q : ℚ[X]) (x : ℝ) : evalReal (p-q) x = evalReal p x-evalReal q x :=
  Polynomial.eval₂_sub _
@[simp] lemma evalReal_mul (p q : ℚ[X]) (x : ℝ) : evalReal (p*q) x = evalReal p x*evalReal q x :=
  Polynomial.eval₂_mul _ _
@[simp] lemma evalReal_pow (p : ℚ[X]) (k : ℕ) (x : ℝ) : evalReal (p^k) x = (evalReal p x)^k :=
  Polynomial.eval₂_pow _ _ _
@[simp] lemma evalReal_C (a : ℚ) (x : ℝ) : evalReal (C a) x = (a:ℝ) :=
  Polynomial.eval₂_C _ _
@[simp] lemma evalReal_X (x : ℝ) : evalReal (X:ℚ[X]) x = x := Polynomial.eval₂_X _ _
@[simp] lemma evalReal_comp (p q : ℚ[X]) (x : ℝ) :
    evalReal (p.comp q) x = evalReal p (evalReal q x) := Polynomial.eval₂_comp _

noncomputable def linearArg (d : ℕ) (η : ℚ) : ℚ[X] := C ((d:ℚ)⁻¹)*X+C η

@[simp] lemma evalReal_linearArg (d : ℕ) (η : ℚ) (x : ℝ) :
    evalReal (linearArg d η) x = x/d + (η:ℝ) := by
  simp only [linearArg, evalReal_add, evalReal_mul, evalReal_C, evalReal_X,
    Rat.cast_inv, Rat.cast_natCast]
  ring

lemma linearArg_natDegree_le (d : ℕ) (η : ℚ) : (linearArg d η).natDegree ≤ 1 := by
  apply poly_add_degree
  · exact (natDegree_C_mul_le _ _).trans (by simp)
  · simp

/-- The exact integral-coordinate polynomial, with the zero slope handled without division. -/
noncomputable def integralPiece (d : ℕ) (η : ℚ) (A G₀ G₁ : ℚ[X]) : ℚ[X] :=
  if η=0 then C ((d:ℚ)⁻¹)*A.comp (linearArg d 0)
  else C (((d:ℚ)*η)⁻¹)*(G₁.comp (linearArg d η)-G₀.comp (linearArg d 0))

lemma integralPiece_natDegree_le (d : ℕ) (η : ℚ) {A G₀ G₁ : ℚ[X]}
    (hA : A.natDegree ≤ 1) (h₀ : G₀.natDegree ≤ 2) (h₁ : G₁.natDegree ≤ 2) :
    (integralPiece d η A G₀ G₁).natDegree ≤ 2 := by
  unfold integralPiece
  split_ifs
  · apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_comp]
    exact (Nat.mul_le_mul hA (linearArg_natDegree_le _ _)).trans (by norm_num)
  · apply (natDegree_C_mul_le _ _).trans
    apply poly_sub_degree
    · rw [natDegree_comp]
      simpa using Nat.mul_le_mul h₁ (linearArg_natDegree_le d η)
    · rw [natDegree_comp]
      simpa using Nat.mul_le_mul h₀ (linearArg_natDegree_le d 0)

lemma evalReal_integralPiece (d : ℕ) (η : ℚ) (A G₀ G₁ : ℚ[X]) (x : ℝ) :
    evalReal (integralPiece d η A G₀ G₁) x =
      if η=0 then (d:ℝ)⁻¹*evalReal A (x/d)
      else ((d:ℝ)*(η:ℝ))⁻¹*(evalReal G₁ (x/d+η)-evalReal G₀ (x/d)) := by
  unfold integralPiece
  split_ifs <;> simp

noncomputable def massPiece (d : ℕ) (η : ℚ) (q₀ q₁ : ℤ) : ℚ[X] :=
  (integralPiece d η (phaseRePiece q₀) (splineRePiece q₀) (splineRePiece q₁))^2+
    (integralPiece d η (phaseImPiece q₀) (splineImPiece q₀) (splineImPiece q₁))^2

lemma massPiece_natDegree_le (d : ℕ) (η : ℚ) (q₀ q₁ : ℤ) :
    (massPiece d η q₀ q₁).natDegree ≤ 4 := by
  apply poly_add_degree
  · apply natDegree_pow_le.trans
    have h := integralPiece_natDegree_le d η (phaseRePiece_natDegree_le q₀)
      (splineRePiece_natDegree_le q₀) (splineRePiece_natDegree_le q₁)
    omega
  · apply natDegree_pow_le.trans
    have h := integralPiece_natDegree_le d η (phaseImPiece_natDegree_le q₀)
      (splineImPiece_natDegree_le q₀) (splineImPiece_natDegree_le q₁)
    omega

lemma massPiece_eq {d : ℕ} (hd : 0 < d) (η : ℚ) {u : ℝ} (hu₀ : 0 ≤ u)
    (hu₁ : u ≤ d) (hη : |(η:ℝ)| ≤ 1/2) (q₀ q₁ : ℤ)
    (hq₀l : (q₀:ℝ)/4 ≤ u/d) (hq₀u : u/d ≤ ((q₀:ℝ)+1)/4)
    (hq₁l : (q₁:ℝ)/4 ≤ u/d+η) (hq₁u : u/d+η ≤ ((q₁:ℝ)+1)/4) :
    evalReal (massPiece d η q₀ q₁) u = ‖residueIntegral d u η‖^2 := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have ha₀ : 0 ≤ u/d := div_nonneg hu₀ hd'.le
  have ha₁ : u/d ≤ 1 := (div_le_one hd').mpr hu₁
  simp only [massPiece, evalReal_add, evalReal_pow, evalReal_integralPiece]
  by_cases h : η=0
  · simp only [h, ite_true, Rat.cast_zero, residueIntegral_zero]
    rw [evalReal_phaseRePiece q₀ hq₀l hq₀u, evalReal_phaseImPiece q₀ hq₀l hq₀u,
      splineReDeriv_eq (by linarith) (by linarith),
      splineImDeriv_eq (by linarith) (by linarith), Complex.sq_norm]
    rw [show (d:ℂ)⁻¹ = (((d:ℝ)⁻¹:ℝ):ℂ) by simp]
    simp [phase, Complex.normSq_apply]
    ring
  · simp only [h, ite_false]
    rw [evalReal_splineRePiece q₀ hq₀l hq₀u, evalReal_splineImPiece q₀ hq₀l hq₀u,
      evalReal_splineRePiece q₁ hq₁l hq₁u, evalReal_splineImPiece q₁ hq₁l hq₁u,
      residueIntegral_eq_primitive hd hu₀ hu₁ hη (by exact_mod_cast h), Complex.sq_norm]
    rw [show (d:ℂ)⁻¹ = (((d:ℝ)⁻¹:ℝ):ℂ) by simp,
      show ((η:ℝ):ℂ)⁻¹ = (((η:ℝ)⁻¹:ℝ):ℂ) by simp]
    simp [spline, Complex.normSq_apply, mul_inv_rev]
    ring

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Upward coefficient rounding by a specified integer denominator. -/
def roundCoeff (D : ℕ) (a : ℚ) : ℚ := (⌈(D:ℚ)*a⌉:ℤ)/(D:ℚ)

lemma roundCoeff_error {D : ℕ} (hD : 0 < D) (a : ℚ) :
    0 ≤ roundCoeff D a-a ∧ roundCoeff D a-a ≤ 1/(D:ℚ) := by
  have hD' : (0:ℚ) < D := Nat.cast_pos.mpr hD
  have hl := Int.le_ceil ((D:ℚ)*a)
  have hu := Int.ceil_lt_add_one ((D:ℚ)*a)
  unfold roundCoeff
  constructor
  · apply sub_nonneg.mpr
    apply (le_div_iff₀ hD').mpr
    linarith
  · rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hD').mpr
    rw [add_mul, div_mul_cancel₀ _ hD'.ne']
    linarith

lemma roundCoeff_error_real {D : ℕ} (hD : 0 < D) (a : ℚ) :
    0 ≤ (roundCoeff D a:ℝ)-(a:ℝ) ∧ (roundCoeff D a:ℝ)-(a:ℝ) ≤ 1/(D:ℝ) := by
  rcases roundCoeff_error hD a with ⟨hl, hu⟩
  constructor
  · have h : (0:ℝ) ≤ ((roundCoeff D a-a:ℚ):ℝ) := Rat.cast_nonneg.mpr hl
    simpa using h
  · have h : ((roundCoeff D a-a:ℚ):ℝ) ≤ ((1/(D:ℚ):ℚ):ℝ) := Rat.cast_le.mpr hu
    simpa using h

noncomputable def roundedValue (D : ℕ) (p : ℚ[X]) (u : ℚ) : ℚ :=
  ∑ q ∈ Finset.range 5, roundCoeff D (p.coeff q)*u^q

lemma roundedValue_error {D : ℕ} (hD : 0 < D) (p : ℚ[X])
    (hp : p.natDegree ≤ 4) {u : ℚ} (hu : 0 ≤ u) :
    0 ≤ (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ∧
      (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ≤
        (∑ q ∈ Finset.range 5, (u:ℝ)^q)/(D:ℝ) := by
  have hu' : (0:ℝ) ≤ u := by exact_mod_cast hu
  have he : (roundedValue D p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) =
      ∑ q ∈ Finset.range 5, ((roundCoeff D (p.coeff q):ℝ)-(p.coeff q:ℝ))*(u:ℝ)^q := by
    rw [Polynomial.eval₂_eq_sum_range' _ (by omega : p.natDegree < 5)]
    simp only [roundedValue, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
      sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun q _ => mul_nonneg (roundCoeff_error_real hD _).1 (pow_nonneg hu' _))
  · calc
      _ ≤ ∑ q ∈ Finset.range 5, (1/(D:ℝ))*(u:ℝ)^q :=
        Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_right
          (roundCoeff_error_real hD _).2 (pow_nonneg hu' _))
      _ = _ := by rw [← Finset.mul_sum]; ring

lemma five_powers_bound {u B : ℝ} (hB : 2 ≤ B) (hu₀ : 0 ≤ u) (huB : u ≤ B) :
    (∑ q ∈ Finset.range 5, u^q) ≤ B^8 := by
  have hB1 : 1 ≤ B := by linarith
  have hs : (∑ q ∈ Finset.range 5, u^q) ≤ 5*B^4 := by
    calc
      _ ≤ ∑ _q ∈ Finset.range 5, B^4 := by
        apply Finset.sum_le_sum
        intro q hq
        exact (pow_le_pow_left₀ hu₀ huB q).trans
          (pow_le_pow_right₀ hB1 (by simp only [Finset.mem_range] at hq; omega))
      _ = _ := by simp
  have hB4 : 16 ≤ B^4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hB 4
    norm_num at h
    exact h
  have h48 : B^8 = (B^4)^2 := by ring
  rw [h48]
  nlinarith

lemma roundedValue_small_error {Q B : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (p : ℚ[X]) (hp : p.natDegree ≤ 4) {u : ℕ} (hu : u ≤ B) :
    0 ≤ (roundedValue (Q*B^8) p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ∧
      (roundedValue (Q*B^8) p u:ℝ)-p.eval₂ (Rat.castHom ℝ) (u:ℝ) ≤ 1/(Q:ℝ) := by
  have hB₀ : 0 < B := by omega
  have hD := Nat.mul_pos hQ (pow_pos hB₀ 8)
  have h := roundedValue_error hD p hp (Nat.cast_nonneg u)
  simp only [Rat.cast_natCast] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB₀
  have hg := five_powers_bound (by exact_mod_cast hB : (2:ℝ) ≤ B)
    (Nat.cast_nonneg u) (by exact_mod_cast hu)
  calc
    _ ≤ (B:ℝ)^8/(Q*B^8) := by
      push_cast
      exact div_le_div_of_nonneg_right hg (mul_nonneg hQ'.le (pow_nonneg hB'.le _))
    _ = 1/(Q:ℝ) := by field_simp

end ExactQuantumFactoring.OrderTrial


namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators Polynomial
open Polynomial

/-- Exact rational form of the nearest-bin error. -/
def binErrorRat (Q d j : ℕ) : ℚ := (bin Q d j : ℚ)-(j:ℚ)*Q/d

@[simp] lemma binErrorRat_cast (Q d j : ℕ) :
    (binErrorRat Q d j:ℝ) = binError Q d j := by simp [binErrorRat, binError]

/-- Half-open quarter assignment, computed only by rational arithmetic. -/
def quarterIndex (x : ℚ) : ℤ := ⌊4*x⌋

lemma quarterIndex_bounds (x : ℚ) :
    (quarterIndex x:ℝ)/4 ≤ (x:ℝ) ∧ (x:ℝ) ≤ ((quarterIndex x:ℝ)+1)/4 := by
  have hl := Int.floor_le (4*x)
  have hu := (Int.lt_floor_add_one (4*x)).le
  change (quarterIndex x:ℚ) ≤ 4*x at hl
  change 4*x ≤ (quarterIndex x:ℚ)+1 at hu
  have hl' : (quarterIndex x:ℝ) ≤ 4*(x:ℝ) := by exact_mod_cast hl
  have hu' : 4*(x:ℝ) ≤ (quarterIndex x:ℝ)+1 := by exact_mod_cast hu
  constructor <;> linarith

noncomputable def selectedMass (d : ℕ) (η u : ℚ) : ℚ[X] :=
  massPiece d η (quarterIndex (u/d)) (quarterIndex (u/d+η))

lemma selectedMass_natDegree_le (d : ℕ) (η u : ℚ) :
    (selectedMass d η u).natDegree ≤ 4 := massPiece_natDegree_le _ _ _ _

lemma selectedMass_eq {d : ℕ} (hd : 0 < d) (η : ℚ) {u : ℕ} (hu : u ≤ d)
    (hη : |(η:ℝ)| ≤ 1/2) :
    evalReal (selectedMass d η u) u = ‖residueIntegral d u η‖^2 := by
  have h₀ := quarterIndex_bounds ((u:ℚ)/d)
  have h₁ := quarterIndex_bounds ((u:ℚ)/d+η)
  push_cast at h₀ h₁
  exact massPiece_eq hd η (Nat.cast_nonneg u) (by exact_mod_cast hu) hη _ _
    h₀.1 h₀.2 h₁.1 h₁.2

/-- Literal majorant from (majorant-construction), retaining Q and B as arguments. -/
noncomputable def majorant (Q B d j u : ℕ) : ℚ :=
  roundedValue (Q*B^8) (selectedMass d (binErrorRat Q d j) u) u + 64/(Q:ℚ)

lemma majorant_ideal_error {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) {u : ℕ} (hu : u ≤ d) :
    64/(Q:ℝ) ≤ (majorant Q B d j u:ℝ)-‖residueIntegral d u (binError Q d j)‖^2 ∧
      (majorant Q B d j u:ℝ)-‖residueIntegral d u (binError Q d j)‖^2 ≤ 65/(Q:ℝ) := by
  have h := roundedValue_small_error hQ hB (selectedMass d (binErrorRat Q d j) u)
    (selectedMass_natDegree_le _ _ _) (hu.trans hdB)
  change 0 ≤ _-evalReal _ _ ∧ _-evalReal _ _ ≤ _ at h
  rw [selectedMass_eq hd _ hu (by simpa using binError_bound (Q:=Q) (j:=j) hd),
    binErrorRat_cast] at h
  simp only [majorant, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  simp only [div_eq_mul_inv] at h ⊢
  constructor <;> linarith [h.1, h.2]

lemma majorant_nonneg {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) {u : ℕ} (hu : u ≤ d) :
    0 ≤ majorant Q B d j u := by
  have h := (majorant_ideal_error hQ hB hd hdB j hu).1
  have hQ' : (0:ℝ) ≤ 64/(Q:ℝ) := by positivity
  have h' : (0:ℝ) ≤ majorant Q B d j u := by nlinarith [sq_nonneg ‖residueIntegral d u (binError Q d j)‖]
  exact_mod_cast h'

/-- Source majorant-error, with the stronger explicit margin 32/Q..97/Q. -/
lemma majorant_probability_error {Q B d t : ℕ} (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (hdQ : d ≤ Q) (ht : t < d) (j : ℕ) :
    32/(Q:ℝ) ≤ (majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t ∧
      (majorant Q B d j ((j*t)%d):ℝ)-residueProbability Q d j t ≤ 97/(Q:ℝ) := by
  have he := residueProbability_integral_error hd hdQ ht j
  rw [abs_le] at he
  have hm := majorant_ideal_error (hd.trans_le hdQ) hB hd hdB j (Nat.mod_lt (j*t) hd).le
  simp only [div_eq_mul_inv] at he hm ⊢
  constructor <;> linarith [he.1, he.2, hm.1, hm.2]

/-- Source half-sum, initially a mathematical sum; bounded-piece evaluation follows. -/
noncomputable def majorantSum (Q B d j : ℕ) : ℚ :=
  (∑ u ∈ Finset.range d, majorant Q B d j u)/2

lemma majorantSum_lower {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) :
    1/(128*(d:ℝ)) ≤ (majorantSum Q B d j:ℝ) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (d:ℝ)*(1/(8*(d:ℝ)))^2 ≤
      ∑ u ∈ Finset.range d, (majorant Q B d j u:ℝ) := by
    calc
      _ = ∑ _u ∈ Finset.range d, (1/(8*(d:ℝ)))^2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro u hu
        have hl := (residueIntegral_bounds hd (u:ℝ) (binError_bound (Q:=Q) (j:=j) hd)).1
        have hp : 0 ≤ 1/(8*(d:ℝ)) := by positivity
        have hl2 := sq_le_sq₀ hp (norm_nonneg _) |>.mpr hl
        have hm := (majorant_ideal_error hQ hB hd hdB j (u:=u) (by simp only [Finset.mem_range] at hu; omega)).1
        have hQ' : (0:ℝ) ≤ 64/(Q:ℝ) := by positivity
        linarith
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  have he : (d:ℝ)*(1/(8*(d:ℝ)))^2/2 = 1/(128*(d:ℝ)) := by field_simp; ring
  rw [← he]
  linarith

lemma majorantSum_upper {Q B d : ℕ} (hQ : 0 < Q) (hB : 2 ≤ B)
    (hd : 0 < d) (hdB : d ≤ B) (j : ℕ) :
    (majorantSum Q B d j:ℝ) ≤ 1/(2*(d:ℝ))+65*d/(2*(Q:ℝ)) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hs : (∑ u ∈ Finset.range d, (majorant Q B d j u:ℝ)) ≤
      (d:ℝ)*((1/(d:ℝ))^2+65/(Q:ℝ)) := by
    calc
      _ ≤ ∑ _u ∈ Finset.range d, ((1/(d:ℝ))^2+65/(Q:ℝ)) := by
        apply Finset.sum_le_sum
        intro u hu
        have hl := (residueIntegral_bounds hd (u:ℝ) (binError_bound (Q:=Q) (j:=j) hd)).2
        have hp : 0 ≤ 1/(d:ℝ) := by positivity
        have hl2 := (sq_le_sq₀ (norm_nonneg _) hp).mpr hl
        have hm := (majorant_ideal_error hQ hB hd hdB j (u:=u) (by simp only [Finset.mem_range] at hu; omega)).2
        linarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [majorantSum, Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat]
  have he : (d:ℝ)*((1/(d:ℝ))^2+65/(Q:ℝ))/2 =
      1/(2*(d:ℝ))+65*d/(2*(Q:ℝ)) := by field_simp
  rw [← he]
  linarith

end ExactQuantumFactoring.OrderTrial



end

end OAI
