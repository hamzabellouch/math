import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPointFieldParameter

namespace OAI

/-! The coupled profile, outgoing column and differentiated column form a
polynomial ten-coordinate ODE with coarse exponential derivative bounds. -/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def spectralParameterState (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄)
    (t : ℝ) : Fin 10 → ℂ :=
  ![(q t).1, (q t).2, (Y t).1.1, (Y t).1.2, (Y t).2.1, (Y t).2.2,
    (Z t).1.1, (Z t).1.2, (Z t).2.1, (Z t).2.2]

@[simp] theorem spectralParameterState_zero (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 0 = (q t).1 := rfl
@[simp] theorem spectralParameterState_one (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 1 = (q t).2 := rfl
@[simp] theorem spectralParameterState_two (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 2 = (Y t).1.1 := rfl
@[simp] theorem spectralParameterState_three (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 3 = (Y t).1.2 := rfl
@[simp] theorem spectralParameterState_four (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 4 = (Y t).2.1 := rfl
@[simp] theorem spectralParameterState_five (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 5 = (Y t).2.2 := rfl

@[simp] theorem spectralParameterState_six (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 6 = (Z t).1.1 := rfl
@[simp] theorem spectralParameterState_seven (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 7 = (Z t).1.2 := rfl
@[simp] theorem spectralParameterState_eight (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 8 = (Z t).2.1 := rfl
@[simp] theorem spectralParameterState_nine (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) :
    spectralParameterState q Y Z t 9 = (Z t).2.2 := rfl

noncomputable def spectralParameterDifferential (ν νp νm eta : ℂ) (m : ℕ) :
    Fin 10 → SpectralParameterExpr :=
  let q := SpectralParameterExpr.coordinate 0
  let dq := SpectralParameterExpr.coordinate 1
  let p := SpectralParameterExpr.coordinate 2
  let dp := SpectralParameterExpr.coordinate 3
  let n := SpectralParameterExpr.coordinate 4
  let dn := SpectralParameterExpr.coordinate 5
  let v := SpectralParameterExpr.coordinate 6
  let dv := SpectralParameterExpr.coordinate 7
  let w := SpectralParameterExpr.coordinate 8
  let dw := SpectralParameterExpr.coordinate 9
  let c := SpectralParameterExpr.constant
  let e := SpectralParameterExpr.exponential
  let a := SpectralParameterExpr.add
  let M := SpectralParameterExpr.mul
  let star := SpectralParameterExpr.conjugate
  let pow := SpectralParameterExpr.pow
  let D := M (c (m + 1)) (M (pow q m) (pow (star q) m))
  let C := M (c m) (M (pow q (m + 1)) (pow (star q) (m - 1)))
  ![dq,
    a (a (M (c (-(2 * ν + 10))) dq) (M (M (c (-Complex.I / 2)) e) dq))
      (a (M (c (-(ν * (ν + 10)))) q) (M (pow q (m + 1)) (pow (star q) m))),
    dp,
    a (a (M (c (-(2 * νp + 10))) dp) (M (M (c (-Complex.I / 2)) e) dp))
      (a (M (c (-(νp * (νp + 10) - eta))) p) (a (M D p) (M C n))),
    dn,
    a (a (M (c (-(2 * νm + 10))) dn) (M (M (c (Complex.I / 2)) e) dn))
      (a (M (c (-(νm * (νm + 10) - eta))) n) (a (M (star D) n) (M (star C) p))),
    dv,
    a (a (a (M (c (-(2 * νp + 10))) dv) (M (M (c (-Complex.I / 2)) e) dv))
      (a (M (c (-(νp * (νp + 10) - eta))) v) (a (M D v) (M C w))))
      (a (M (c 4) dp) (M (c (4*νp+20)) p)),
    dw,
    a (a (a (M (c (-(2 * νm + 10))) dw) (M (M (c (Complex.I / 2)) e) dw))
      (a (M (c (-(νm * (νm + 10) - eta))) w) (a (M (star D) w) (M (star C) v))))
      (a (M (c 4) dn) (M (c (4*νm+20)) n))]

theorem spectralParameterDifferential_eval (ν νp νm eta : ℂ) (m : ℕ)
    (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ) (i : Fin 10) :
    SpectralParameterExpr.eval (spectralParameterState q Y Z) t
      (spectralParameterDifferential ν νp νm eta m i) =
      spectralParameterState
        (fun _ => radialExteriorODEField ν m t (q t))
        (fun _ => circularLeadingField t (Y t) +
          circularBoundedField νp νm eta m (q t).1 (Y t))
        (fun _ => circularLeadingField t (Z t) +
          circularBoundedField νp νm eta m (q t).1 (Z t) + circularPointSlopeCLM νp νm 0 (Y t)) t i := by
  fin_cases i <;>
    simp only [spectralParameterDifferential, SpectralParameterExpr.eval,
      SpectralParameterExpr.eval_pow, spectralParameterState_zero,
      spectralParameterState_one, spectralParameterState_two, spectralParameterState_three,
      spectralParameterState_four, spectralParameterState_five,
      spectralParameterState_six, spectralParameterState_seven,
      spectralParameterState_eight, spectralParameterState_nine,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      radialExteriorODEField, circularLeadingField, circularBoundedField,
      spectralDiagonalCoefficient, spectralCrossCoefficient, oddPowerNonlinearity,
      Complex.ofReal_div, Complex.ofReal_ofNat,
      star_add, star_mul, star_natCast, star_one, Nat.cast_add, Nat.cast_one,
      circularPointSlopeCLM,LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk,AddHom.coe_mk,mul_zero,sub_zero]
  all_goals simp only [spectralParameterState, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Prod.fst_add, Prod.snd_add]
  all_goals ring

theorem spectralParameterState_hasDerivAt (ν νp νm eta : ℂ) (m : ℕ)
    (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t : ℝ)
    (hq : HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (q t).1 (Y t)) t)
    (hZ : HasDerivAt Z (circularLeadingField t (Z t) +
      circularBoundedField νp νm eta m (q t).1 (Z t) + circularPointSlopeCLM νp νm 0 (Y t)) t)
    (i : Fin 10) :
    HasDerivAt (fun s => spectralParameterState q Y Z s i)
      (SpectralParameterExpr.eval (spectralParameterState q Y Z) t
        (spectralParameterDifferential ν νp νm eta m i)) t := by
  rw [spectralParameterDifferential_eval]
  have hq₀ := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hq
  have hq₁ := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hq
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hn := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hv := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hZ
  have hw := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hZ
  fin_cases i
  · exact hq₀
  · exact hq₁
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hp
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hp
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hn
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hn
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hv
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hv
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hw
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hw

theorem spectralParameterState_bound (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄) (t M : ℝ)
    (hq : ‖q t‖ ≤ M) (hY : ‖Y t‖ ≤ M) (hZ : ‖Z t‖ ≤ M) (i : Fin 10) :
    ‖spectralParameterState q Y Z t i‖ ≤ M := by
  fin_cases i
  · exact (norm_fst_le _).trans hq
  · exact (norm_snd_le _).trans hq
  · exact (norm_fst_le _).trans ((norm_fst_le _).trans hY)
  · exact (norm_snd_le _).trans ((norm_fst_le _).trans hY)
  · exact (norm_fst_le _).trans ((norm_snd_le _).trans hY)
  · exact (norm_snd_le _).trans ((norm_snd_le _).trans hY)
  · exact (norm_fst_le _).trans ((norm_fst_le _).trans hZ)
  · exact (norm_snd_le _).trans ((norm_fst_le _).trans hZ)
  · exact (norm_fst_le _).trans ((norm_snd_le _).trans hZ)
  · exact (norm_snd_le _).trans ((norm_snd_le _).trans hZ)

theorem spectralParameter_derivatives_exponential_bound
    (ν νp νm eta : ℂ) (m : ℕ) (q : ℝ → ℂ × ℂ) (Y Z : ℝ → V₄)
    (L U M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ t, L < t → HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : ∀ t, L < t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (q t).1 (Y t)) t)
    (hZ : ∀ t, L < t → HasDerivAt Z (circularLeadingField t (Z t) +
      circularBoundedField νp νm eta m (q t).1 (Z t) + circularPointSlopeCLM νp νm 0 (Y t)) t)
    (hbq : ∀ t, U ≤ t → ‖q t‖ ≤ M) (hbY : ∀ t, U ≤ t → ‖Y t‖ ≤ M)
    (hbZ : ∀ t, U ≤ t → ‖Z t‖ ≤ M)
    (i : Fin 10) (k : ℕ) :
    ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ L < T ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k (fun s => spectralParameterState q Y Z s i) t‖ ≤
        B * Real.exp (C * t) := by
  exact SpectralParameterExpr.derivatives_exponential_bound
    (spectralParameterDifferential ν νp νm eta m) (spectralParameterState q Y Z) L U M hM
    (fun t ht => spectralParameterState_hasDerivAt ν νp νm eta m q Y Z t
      (hq t ht) (hY t ht) (hZ t ht))
    (fun t ht i => spectralParameterState_bound q Y Z t M (hbq t ht) (hbY t ht) (hbZ t ht) i) i k

end DefocusingNLS

end OAI
