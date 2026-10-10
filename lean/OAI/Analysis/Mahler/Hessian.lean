import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

namespace OAI

open Complex
open scoped BigOperators Topology

local notation "conj" => starRingEnd ℂ

namespace Mahler
variable {E : Type*} [normedAddCommGroupE : NormedAddCommGroup E] [normedSpaceComplexE : NormedSpace ℂ E]
  [normedSpaceRealE : NormedSpace ℝ E] [isScalarTowerRealComplexE : IsScalarTower ℝ ℂ E]

/-- Wirtinger derivative, defined from the real Frechet derivative. -/
noncomputable def dz (u : E → ℂ) (x v : E) : ℂ :=
  (fderiv ℝ u x v - I * fderiv ℝ u x (I • v)) / 2
/-- Conjugate Wirtinger derivative with the same normalization. -/
noncomputable def dbar (u : E → ℂ) (x v : E) : ℂ :=
  (fderiv ℝ u x v + I * fderiv ℝ u x (I • v)) / 2

lemma dz_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dz f x v = fderiv ℂ f x v := by
  rw [dz, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v - I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  have hi := I_mul_I
  calc
    _ = (fderiv ℂ f x v - (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [hi]; ring

lemma dbar_holomorphic {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℂ f x) :
    dbar f x v = 0 := by
  rw [dbar, (hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  change (fderiv ℂ f x v + I * fderiv ℂ f x (I • v)) / 2 = _
  rw [map_smul]
  simp only [smul_eq_mul]
  calc
    _ = (fderiv ℂ f x v + (I * I) * fderiv ℂ f x v) / 2 := by ring
    _ = _ := by rw [I_mul_I]; ring

omit isScalarTowerRealComplexE in
lemma dz_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dz (fun y => conj (f y)) x v = conj (dbar f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dz, h.fderiv]
  simp [dbar, map_add, map_mul, conj_I, map_ofNat, sub_eq_add_neg]

omit isScalarTowerRealComplexE in
lemma dbar_conj [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : DifferentiableAt ℝ f x) :
    dbar (fun y => conj (f y)) x v = conj (dz f x v) := by
  have h : HasFDerivAt (fun y => conj (f y))
      (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f x)) x :=
    Complex.conjCLE.hasFDerivAt.comp x hf.hasFDerivAt
  rw [dbar, h.fderiv]
  simp [dz, map_sub, map_mul, conj_I, map_ofNat]

omit isScalarTowerRealComplexE in
lemma dz_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dz (fun y => f y * g y) x v = dz f x v * g x + f x * dz g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dz, h.fderiv]
  simp [dz]
  ; ring

omit isScalarTowerRealComplexE in
lemma dbar_mul [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dbar (fun y => f y * g y) x v = dbar f x v * g x + f x * dbar g x v := by
  have h := hf.hasFDerivAt.mul hg.hasFDerivAt
  simp only [Pi.mul_def] at h
  rw [dbar, h.fderiv]
  simp [dbar]
  ; ring

omit isScalarTowerRealComplexE in
lemma dz_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dz (fun y => ∑ j, f j y) x v = ∑ j, dz (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dz, h.fderiv]
  simp only [dz, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

omit isScalarTowerRealComplexE in
lemma dbar_sum [IsScalarTower ℝ ℂ E] {ι : Type*} [Fintype ι] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    dbar (fun y => ∑ j, f j y) x v = ∑ j, dbar (f j) x v := by
  have h : HasFDerivAt (fun y => ∑ j, f j y) (∑ j, fderiv ℝ (f j) x) x :=
    HasFDerivAt.fun_sum (fun j _ => (hf j).hasFDerivAt)
  rw [dbar, h.fderiv]
  simp only [dbar, sum_apply, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

omit isScalarTowerRealComplexE in
lemma dz_clog [IsScalarTower ℝ ℂ E] {u : E → ℂ} {x v : E} (hu : DifferentiableAt ℝ u x)
    (hp : u x ∈ slitPlane) :
    dz (fun y => Complex.log (u y)) x v = dz u x v / u x := by
  have h := ((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x hu.hasFDerivAt
  change HasFDerivAt (fun y => Complex.log (u y)) _ x at h
  rw [dz, h.fderiv]
  simp [dz, ContinuousLinearMap.comp_apply, div_eq_mul_inv]
  ; ring

omit isScalarTowerRealComplexE in
lemma dbar_div [IsScalarTower ℝ ℂ E] {f g : E → ℂ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (hn : g x ≠ 0) :
    dbar (fun y => f y / g y) x v =
      (dbar f x v * g x - f x * dbar g x v) / g x ^ 2 := by
  have hi := ((hasDerivAt_inv hn).hasFDerivAt.restrictScalars ℝ).comp x hg.hasFDerivAt
  change HasFDerivAt (fun y => (g y)⁻¹) _ x at hi
  have h := hf.hasFDerivAt.mul hi
  simp only [Pi.mul_def] at h
  simp only [div_eq_mul_inv]
  rw [dbar, h.fderiv]
  simp [dbar]
  ; field_simp [hn]
  ; ring

variable {ι : Type*} [Fintype ι]
/-- The squared Euclidean norm of a finite holomorphic map. -/
noncomputable def tau (f : ι → E → ℂ) (x : E) : ℝ := ∑ j, normSq (f j x)
noncomputable def energy (f : ι → E → ℂ) (x : E) : ℂ := ∑ j, conj (f j x) * f j x
noncomputable def logTau (f : ι → E → ℂ) (x : E) : ℂ := (Real.log (tau f x) : ℂ)

omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma tau_nonneg [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : 0 ≤ tau f x :=
  Finset.sum_nonneg (fun j _ => normSq_nonneg (f j x))
omit normedAddCommGroupE normedSpaceComplexE normedSpaceRealE isScalarTowerRealComplexE in
lemma energy_eq_tau [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (f : ι → E → ℂ) (x : E) : energy f x = (tau f x : ℂ) := by
  simp [energy, tau, Complex.normSq_eq_conj_mul_self]
lemma logTau_eq (f : ι → E → ℂ) : logTau f = fun x => Complex.log (energy f x) := by
  funext x
  rw [logTau, energy_eq_tau, Complex.ofReal_log (tau_nonneg f x)]

omit normedSpaceComplexE isScalarTowerRealComplexE in
lemma diff_conj [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x :=
  Complex.conjCLE.differentiableAt.comp x hf

lemma differentiable_energy {f : ι → E → ℂ} {x : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) : DifferentiableAt ℝ (energy f) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj ((hf j).restrictScalars ℝ)).mul ((hf j).restrictScalars ℝ))

lemma dz_energy {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) :
    dz (energy f) x v = ∑ j, conj (f j x) * fderiv ℂ (f j) x v := by
  change dz (fun y => ∑ j, conj (f j y) * f j y) x v = _
  rw [dz_sum (f := fun j y => conj (f j y) * f j y) (fun j => (diff_conj ((hf j).restrictScalars ℝ)).mul
    ((hf j).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dz_mul (diff_conj ((hf j).restrictScalars ℝ)) ((hf j).restrictScalars ℝ),
    dz_conj ((hf j).restrictScalars ℝ), dbar_holomorphic (hf j), dz_holomorphic (hf j)]
  simp

lemma dbar_energy {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) :
    dbar (energy f) x v = ∑ j, conj (fderiv ℂ (f j) x v) * f j x := by
  change dbar (fun y => ∑ j, conj (f j y) * f j y) x v = _
  rw [dbar_sum (f := fun j y => conj (f j y) * f j y) (fun j => (diff_conj ((hf j).restrictScalars ℝ)).mul
    ((hf j).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar_mul (diff_conj ((hf j).restrictScalars ℝ)) ((hf j).restrictScalars ℝ),
    dbar_conj ((hf j).restrictScalars ℝ), dz_holomorphic (hf j), dbar_holomorphic (hf j)]
  simp

lemma dz_logTau {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    dz (logTau f) x v = (∑ j, conj (f j x) * fderiv ℂ (f j) x v) / (tau f x : ℂ) := by
  rw [logTau_eq, dz_clog (differentiable_energy hf) (by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht), dz_energy hf,
    energy_eq_tau]

omit isScalarTowerRealComplexE in
lemma dbar_congr_nhds [IsScalarTower ℝ ℂ E] {u q : E → ℂ} {x v : E} (h : u =ᶠ[𝓝 x] q) :
    dbar u x v = dbar q x v := by
  simp only [dbar, h.fderiv_eq]

noncomputable def numerator (f : ι → E → ℂ) (v x : E) : ℂ :=
  ∑ j, conj (f j x) * fderiv ℂ (f j) x v

omit normedSpaceRealE isScalarTowerRealComplexE in
lemma diff_first [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {f : E → ℂ} {x v : E} (hf : AnalyticAt ℂ f x) :
    DifferentiableAt ℂ (fun y => fderiv ℂ f y v) x := by
  exact hf.fderiv.differentiableAt.clm_apply (differentiableAt_const v)

lemma diff_numerator {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) : DifferentiableAt ℝ (numerator f v) x := by
  exact DifferentiableAt.fun_sum (fun j _ =>
    (diff_conj ((hf j).differentiableAt.restrictScalars ℝ)).mul
    ((diff_first (hf j)).restrictScalars ℝ))

lemma dbar_numerator {f : ι → E → ℂ} {x v w : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    dbar (numerator f v) x w = ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  change dbar (fun y => ∑ j, conj (f j y) * fderiv ℂ (f j) y v) x w = _
  rw [dbar_sum (f := fun j y => conj (f j y) * fderiv ℂ (f j) y v) (fun j => (diff_conj ((hf j).differentiableAt.restrictScalars ℝ)).mul
    ((diff_first (hf j)).restrictScalars ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  rw [dbar_mul (diff_conj ((hf j).differentiableAt.restrictScalars ℝ))
    ((diff_first (hf j)).restrictScalars ℝ),
    dbar_conj ((hf j).differentiableAt.restrictScalars ℝ),
    dz_holomorphic (hf j).differentiableAt, dbar_holomorphic (diff_first (hf j))]
  simp

/-- Actual mixed Wirtinger derivative of the squared norm. -/
theorem mixed_energy {f : ι → E → ℂ} {x v w : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    dbar (fun y => dz (energy f) y v) x w =
      ∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, AnalyticAt ℂ (f j) y :=
    Filter.eventually_all.mpr (fun j => (hf j).eventually_analyticAt)
  have he : (fun y => dz (energy f) y v) =ᶠ[𝓝 x] numerator f v := by
    filter_upwards [hh] with y hy
    exact dz_energy (fun j => (hy j).differentiableAt)
  rw [dbar_congr_nhds he, dbar_numerator hf]

/-- Actual mixed derivative of the real logarithm, on the positive tau domain. -/
theorem mixed_logTau {f : ι → E → ℂ} {x v w : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    dbar (fun y => dz (logTau f) y v) x w =
      ((tau f x : ℂ) * (∑ j, conj (fderiv ℂ (f j) x w) * fderiv ℂ (f j) x v)
        - (∑ j, conj (f j x) * fderiv ℂ (f j) x v) *
          (∑ j, conj (fderiv ℂ (f j) x w) * f j x)) / (tau f x : ℂ)^2 := by
  have hh : ∀ᶠ y in 𝓝 x, ∀ j, AnalyticAt ℂ (f j) y :=
    Filter.eventually_all.mpr (fun j => (hf j).eventually_analyticAt)
  have hc : ContinuousAt (tau f) x := by
    have h := Complex.continuous_re.continuousAt.comp
      (differentiable_energy (fun j => (hf j).differentiableAt)).continuousAt
    simpa only [Function.comp_def, energy_eq_tau, Complex.ofReal_re] using h
  have hp : ∀ᶠ y in 𝓝 x, 0 < tau f y := hc.eventually (lt_mem_nhds ht)
  have he : (fun y => dz (logTau f) y v) =ᶠ[𝓝 x]
      (fun y => numerator f v y / energy f y) := by
    filter_upwards [hh, hp] with y hy hty
    simpa only [numerator, energy_eq_tau] using dz_logTau
      (v := v) (fun j => (hy j).differentiableAt) hty
  rw [dbar_congr_nhds he, dbar_div (diff_numerator hf)
    (differentiable_energy (fun j => (hf j).differentiableAt)) (by
      rw [energy_eq_tau]; exact_mod_cast ne_of_gt ht),
    dbar_numerator hf, dbar_energy (fun j => (hf j).differentiableAt), energy_eq_tau]
  simp only [numerator]
  ring

end Mahler

end OAI
