import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralGrowth

namespace OAI

/-! # Applying polynomial derivative growth to the actual circular equation -/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V₄" => (ℂ × ℂ) × (ℂ × ℂ)

noncomputable def homogeneousSpectralState (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄)
    (t : ℝ) : Fin 6 → ℂ :=
  ![(q t).1, (q t).2, (Y t).1.1, (Y t).1.2, (Y t).2.1, (Y t).2.2]

@[simp] theorem homogeneousSpectralState_zero (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) :
    homogeneousSpectralState q Y t 0 = (q t).1 := rfl
@[simp] theorem homogeneousSpectralState_one (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) :
    homogeneousSpectralState q Y t 1 = (q t).2 := rfl
@[simp] theorem homogeneousSpectralState_two (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) :
    homogeneousSpectralState q Y t 2 = (Y t).1.1 := rfl
@[simp] theorem homogeneousSpectralState_three (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) :
    homogeneousSpectralState q Y t 3 = (Y t).1.2 := rfl
@[simp] theorem homogeneousSpectralState_four (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) :
    homogeneousSpectralState q Y t 4 = (Y t).2.1 := rfl
@[simp] theorem homogeneousSpectralState_five (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) :
    homogeneousSpectralState q Y t 5 = (Y t).2.2 := rfl

noncomputable def homogeneousSpectralDifferential (ν νp νm eta : ℂ) (m : ℕ) :
    Fin 6 → HomogeneousSpectralExpr :=
  let q := HomogeneousSpectralExpr.coordinate 0
  let dq := HomogeneousSpectralExpr.coordinate 1
  let p := HomogeneousSpectralExpr.coordinate 2
  let dp := HomogeneousSpectralExpr.coordinate 3
  let n := HomogeneousSpectralExpr.coordinate 4
  let dn := HomogeneousSpectralExpr.coordinate 5
  let c := HomogeneousSpectralExpr.constant
  let e := HomogeneousSpectralExpr.exponential
  let a := HomogeneousSpectralExpr.add
  let M := HomogeneousSpectralExpr.mul
  let star := HomogeneousSpectralExpr.conjugate
  let pow := HomogeneousSpectralExpr.pow
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
      (a (M (c (-(νm * (νm + 10) - eta))) n) (a (M (star D) n) (M (star C) p)))]

theorem homogeneousSpectralDifferential_eval (ν νp νm eta : ℂ) (m : ℕ)
    (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ) (i : Fin 6) :
    HomogeneousSpectralExpr.eval (homogeneousSpectralState q Y) t
      (homogeneousSpectralDifferential ν νp νm eta m i) =
      homogeneousSpectralState
        (fun _ => radialExteriorODEField ν m t (q t))
        (fun _ => circularLeadingField t (Y t) +
          circularBoundedField νp νm eta m (q t).1 (Y t)) t i := by
  fin_cases i <;>
    simp only [homogeneousSpectralDifferential, HomogeneousSpectralExpr.eval,
      HomogeneousSpectralExpr.eval_pow, homogeneousSpectralState_zero,
      homogeneousSpectralState_one, homogeneousSpectralState_two, homogeneousSpectralState_three,
      homogeneousSpectralState_four, homogeneousSpectralState_five,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      radialExteriorODEField, circularLeadingField, circularBoundedField,
      spectralDiagonalCoefficient, spectralCrossCoefficient, oddPowerNonlinearity,
      Complex.ofReal_div, Complex.ofReal_ofNat,
      star_add, star_mul, star_natCast, star_one, Nat.cast_add, Nat.cast_one]
  all_goals simp only [homogeneousSpectralState, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Prod.fst_add, Prod.snd_add]
  all_goals ring

theorem homogeneousSpectralState_hasDerivAt (ν νp νm eta : ℂ) (m : ℕ)
    (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t : ℝ)
    (hq : HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (q t).1 (Y t)) t) (i : Fin 6) :
    HasDerivAt (fun s => homogeneousSpectralState q Y s i)
      (HomogeneousSpectralExpr.eval (homogeneousSpectralState q Y) t
        (homogeneousSpectralDifferential ν νp νm eta m i)) t := by
  rw [homogeneousSpectralDifferential_eval]
  have hq₀ := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hq
  have hq₁ := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hq
  have hp := (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  have hn := (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt t hY
  fin_cases i
  · exact hq₀
  · exact hq₁
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hp
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hp
  · exact (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hn
  · exact (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hn

theorem homogeneousSpectralState_bound (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (t M : ℝ)
    (hq : ‖q t‖ ≤ M) (hY : ‖Y t‖ ≤ M) (i : Fin 6) :
    ‖homogeneousSpectralState q Y t i‖ ≤ M := by
  fin_cases i
  · exact (norm_fst_le _).trans hq
  · exact (norm_snd_le _).trans hq
  · exact (norm_fst_le _).trans ((norm_fst_le _).trans hY)
  · exact (norm_snd_le _).trans ((norm_fst_le _).trans hY)
  · exact (norm_fst_le _).trans ((norm_snd_le _).trans hY)
  · exact (norm_snd_le _).trans ((norm_snd_le _).trans hY)

theorem homogeneousSpectral_derivatives_exponential_bound
    (ν νp νm eta : ℂ) (m : ℕ) (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄)
    (L U M : ℝ) (hM : 0 ≤ M)
    (hq : ∀ t, L < t → HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : ∀ t, L < t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (q t).1 (Y t)) t)
    (hbq : ∀ t, U ≤ t → ‖q t‖ ≤ M) (hbY : ∀ t, U ≤ t → ‖Y t‖ ≤ M)
    (i : Fin 6) (k : ℕ) :
    ∃ C B T : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ L < T ∧ ∀ t, T ≤ t →
      ‖iteratedDeriv k (fun s => homogeneousSpectralState q Y s i) t‖ ≤
        B * Real.exp (C * t) := by
  exact HomogeneousSpectralExpr.derivatives_exponential_bound
    (homogeneousSpectralDifferential ν νp νm eta m) (homogeneousSpectralState q Y) L U M hM
    (fun t ht => homogeneousSpectralState_hasDerivAt ν νp νm eta m q Y t
      (hq t ht) (hY t ht))
    (fun t ht i => homogeneousSpectralState_bound q Y t M (hbq t ht) (hbY t ht) i) i k

noncomputable def homogeneousCoupledSpectralField (ν νp νm eta : ℂ) (m : ℕ)
    (t : ℝ) (w : (ℂ × ℂ) × V₄) : (ℂ × ℂ) × V₄ :=
  (radialExteriorODEField ν m t w.1,
    circularLeadingField t w.2 + circularBoundedField νp νm eta m w.1.1 w.2)

theorem homogeneousCoupledSpectralField_contDiff (ν νp νm eta : ℂ) (m : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (homogeneousCoupledSpectralField ν νp νm eta m)) := by
  have he : ContDiff ℝ ∞ (fun z : ℝ × ((ℂ × ℂ) × V₄) =>
      ((Real.exp (2 * z.1) / 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).div_const 2)
  have hstar : ContDiff ℝ ∞ (star : ℂ → ℂ) :=
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff
  unfold Function.uncurry homogeneousCoupledSpectralField radialExteriorODEField
    circularLeadingField circularBoundedField spectralDiagonalCoefficient
    spectralCrossCoefficient oddPowerNonlinearity
  fun_prop

theorem homogeneousSpectral_solution_contDiffOn
    (ν νp νm eta : ℂ) (m : ℕ) (q : ℝ → ℂ × ℂ) (Y : ℝ → V₄) (L : ℝ)
    (hq : ∀ t, L < t → HasDerivAt q (radialExteriorODEField ν m t (q t)) t)
    (hY : ∀ t, L < t → HasDerivAt Y (circularLeadingField t (Y t) +
      circularBoundedField νp νm eta m (q t).1 (Y t)) t) :
    ContDiffOn ℝ ∞ Y (Ioi L) := by
  have hZ : ContDiffOn ℝ ∞ (fun t => (q t, Y t)) (Ioi L) := by
    intro r hr
    change L < r at hr
    have hI : Icc ((r + L) / 2) (r + 1) ⊆ Ioi L := fun t ht => by
      change L < t
      linarith [ht.1]
    have hF := (homogeneousCoupledSpectralField_contDiff ν νp νm eta m).contDiffOn
      (s := Icc ((r + L) / 2) (r + 1) ×ˢ (univ : Set ((ℂ × ℂ) × V₄)))
    have hh := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤) hF
      (fun t ht => ((hq t (hI ht)).prodMk (hY t (hI ht))).hasDerivWithinAt)
      (fun _ _ => mem_univ _)
    exact (hh r ⟨by linarith, by linarith⟩).contDiffAt
      (Icc_mem_nhds (by linarith) (by linarith)) |>.contDiffWithinAt
  exact hZ.snd

end DefocusingNLS

end OAI
