import Mathlib
import OAI.Geometry.HypersurfaceGerms.CriticalBounds
import OAI.Geometry.HypersurfaceGerms.Preparation

namespace OAI

/-! Chart differentials and isolation of the prepared equations. -/

noncomputable section

namespace AmbientMultiplicity.ChartDifferential
open Filter Topology
abbrev V (n : ℕ) := Fin n → ℂ
abbrev proj {n : ℕ} (i : Fin n) : V n →L[ℂ] ℂ := ContinuousLinearMap.proj i

def H (X T : ℂ) : ℂ := T * (X - T ^ 2) * (X - 2 * T ^ 2)
def HX (X T : ℂ) : ℂ := T * (2 * X - 3 * T ^ 2)
def HT (X T : ℂ) : ℂ := X ^ 2 - 9 * T ^ 2 * X + 10 * T ^ 4

lemma H_deriv {n : ℕ} {X T : V n → ℂ} {DX DT : V n →L[ℂ] ℂ} {x : V n}
    (hX : HasFDerivAt X DX x) (hT : HasFDerivAt T DT x) :
    HasFDerivAt (fun z => H (X z) (T z))
      (HX (X x) (T x) • DX + HT (X x) (T x) • DT) x := by
  convert! (hT.mul (hX.sub (hT.pow 2))).mul
    (hX.sub ((hT.pow 2).const_mul 2)) using 1
  ext v
  simp only [add_apply, smul_apply, sub_apply, smul_eq_mul]
  dsimp [HX, HT]
  ring

def perturbation (a b : ℕ) (x : V 4) : ℂ := x 3 * (x 1 ^ a + x 2 ^ b)

def perturbationD (a b : ℕ) (x : V 4) : V 4 →L[ℂ] ℂ :=
  (x 1 ^ a + x 2 ^ b) • proj 3 +
  (x 3 * a * x 1 ^ (a - 1)) • proj 1 +
  (x 3 * b * x 2 ^ (b - 1)) • proj 2

lemma perturbation_deriv (a b : ℕ) (x : V 4) :
    HasFDerivAt (perturbation a b) (perturbationD a b x) x := by
  convert! ((proj (3 : Fin 4)).hasFDerivAt (x := x)).mul
    ((((proj (1 : Fin 4)).hasFDerivAt (x := x)).pow a).add
      (((proj (2 : Fin 4)).hasFDerivAt (x := x)).pow b)) using 1
  ext v
  simp only [perturbationD, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.add_apply]
  ring

lemma linear_three (L : V 3 →L[ℂ] ℂ) (v : V 3) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) + v 2 * L (Pi.single 2 1) := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

 

lemma multiplier_coordinates (E : V 4 →L[ℂ] ℂ) (A B RA RB RU U Y Z PY PZ : ℂ)
    (hRA : RA ≠ 0)
    (hF : A • E + B • proj 0 + U • proj 3 + PY • proj 1 + PZ • proj 2 = 0)
    (hR : RA • E + RB • proj 0 + RU • proj 3 - Z • proj 1 - Y • proj 2 = 0) :
    ∃ χ : ℂ, A = -χ * RA ∧ B = -χ * RB ∧ U = -χ * RU ∧ PY = χ * Z ∧ PZ = χ * Y := by
  have hF' (i : Fin 4) := congrArg (fun L : V 4 →L[ℂ] ℂ => L (Pi.single i 1)) hF
  have hR' (i : Fin 4) := congrArg (fun L : V 4 →L[ℂ] ℂ => L (Pi.single i 1)) hR
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, zero_apply] at hF' hR'
  have h0F : A * E (Pi.single 0 1) + B = 0 := by simpa using hF' 0
  have h0R : RA * E (Pi.single 0 1) + RB = 0 := by simpa using hR' 0
  have h1F : A * E (Pi.single 1 1) + PY = 0 := by simpa using hF' 1
  have h1R : RA * E (Pi.single 1 1) - Z = 0 := by simpa using hR' 1
  have h2F : A * E (Pi.single 2 1) + PZ = 0 := by simpa using hF' 2
  have h2R : RA * E (Pi.single 2 1) - Y = 0 := by simpa using hR' 2
  have h3F : A * E (Pi.single 3 1) + U = 0 := by simpa using hF' 3
  have h3R : RA * E (Pi.single 3 1) + RU = 0 := by simpa using hR' 3
  refine ⟨-A / RA, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
  all_goals field_simp
  · linear_combination RA * h0F - A * h0R
  · linear_combination RA * h3F - A * h3R
  · linear_combination RA * h1F - A * h1R
  · linear_combination RA * h2F - A * h2R

def base0 (E : V 4 → ℂ) (x : V 4) : V 3 := ![E x, x 0, x 3]
def base1 (E : V 4 → ℂ) (x : V 4) : V 3 := ![x 0, E x, x 3]
def restricted0 (E : V 4 → ℂ) (a b : ℕ) (x : V 4) : ℂ := H (E x) (x 0) + perturbation a b x
def restricted1 (E : V 4 → ℂ) (a b : ℕ) (x : V 4) : ℂ := H (x 0) (E x) + perturbation a b x

def partDeriv (R : V 3 → ℂ) (z : V 3) (i : Fin 3) : ℂ := fderiv ℂ R z (Pi.single i 1)

lemma base0_deriv {E : V 4 → ℂ} {DE : V 4 →L[ℂ] ℂ} {x : V 4}
    (he : HasFDerivAt E DE x) :
    HasFDerivAt (base0 E) (ContinuousLinearMap.pi ![DE, proj 0, proj 3]) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact he
  all_goals exact (proj _).hasFDerivAt

lemma base1_deriv {E : V 4 → ℂ} {DE : V 4 →L[ℂ] ℂ} {x : V 4}
    (he : HasFDerivAt E DE x) :
    HasFDerivAt (base1 E) (ContinuousLinearMap.pi ![proj 0, DE, proj 3]) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (proj _).hasFDerivAt
  · exact he
  · exact (proj _).hasFDerivAt

lemma root_base0_deriv {E : V 4 → ℂ} {DE : V 4 →L[ℂ] ℂ} {x : V 4} {R : V 3 → ℂ}
    (he : HasFDerivAt E DE x) (hr : DifferentiableAt ℂ R (base0 E x)) :
    HasFDerivAt (fun x => R (base0 E x))
      (partDeriv R (base0 E x) 0 • DE + partDeriv R (base0 E x) 1 • proj 0 +
        partDeriv R (base0 E x) 2 • proj 3) x := by
  convert! hr.hasFDerivAt.comp x (base0_deriv he) using 1
  ext v
  dsimp [ContinuousLinearMap.comp_apply]
  rw [linear_three]
  simp only [partDeriv, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp
  ring

lemma root_base1_deriv {E : V 4 → ℂ} {DE : V 4 →L[ℂ] ℂ} {x : V 4} {R : V 3 → ℂ}
    (he : HasFDerivAt E DE x) (hr : DifferentiableAt ℂ R (base1 E x)) :
    HasFDerivAt (fun x => R (base1 E x))
      (partDeriv R (base1 E x) 1 • DE + partDeriv R (base1 E x) 0 • proj 0 +
        partDeriv R (base1 E x) 2 • proj 3) x := by
  convert! hr.hasFDerivAt.comp x (base1_deriv he) using 1
  ext v
  dsimp [ContinuousLinearMap.comp_apply]
  rw [linear_three]
  simp only [partDeriv, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp
  ring

 

theorem critical_chart0 {E : V 4 → ℂ} {x : V 4} {R : V 3 → ℂ} (a b : ℕ)
    (he : DifferentiableAt ℂ E x) (hr : DifferentiableAt ℂ R (base0 E x))
    (hunit : partDeriv R (base0 E x) 0 ≠ 0)
    (hgraph : (fun z => R (base0 E z)) =ᶠ[𝓝 x] (fun z => z 1 * z 2))
    (hcrit : fderiv ℂ (restricted0 E a b) x = 0) :
    ∃ χ : ℂ,
      HX (E x) (x 0) = -χ * partDeriv R (base0 E x) 0 ∧
      HT (E x) (x 0) = -χ * partDeriv R (base0 E x) 1 ∧
      x 1 ^ a + x 2 ^ b = -χ * partDeriv R (base0 E x) 2 ∧
      (a : ℂ) * x 3 * x 1 ^ (a - 1) = χ * x 2 ∧
      (b : ℂ) * x 3 * x 2 ^ (b - 1) = χ * x 1 := by
  have hF := (H_deriv he.hasFDerivAt ((proj (0 : Fin 4)).hasFDerivAt (x := x))).add
    (perturbation_deriv a b x)
  have hFeq : HX (E x) (x 0) • fderiv ℂ E x + HT (E x) (x 0) • proj 0 +
      (x 1 ^ a + x 2 ^ b) • proj 3 +
      ((a : ℂ) * x 3 * x 1 ^ (a - 1)) • proj 1 +
      ((b : ℂ) * x 3 * x 2 ^ (b - 1)) • proj 2 = 0 := by
    have hh : fderiv ℂ (restricted0 E a b) x = _ := hF.fderiv
    rw [hcrit] at hh
    rw [hh]
    simp only [perturbationD, ContinuousLinearMap.proj_apply]
    module
  have hR := root_base0_deriv he.hasFDerivAt hr
  have hYZ := ((proj (1 : Fin 4)).hasFDerivAt (x := x)).mul
    ((proj (2 : Fin 4)).hasFDerivAt (x := x))
  have hReq : partDeriv R (base0 E x) 0 • fderiv ℂ E x + partDeriv R (base0 E x) 1 • proj 0 +
      partDeriv R (base0 E x) 2 • proj 3 - x 2 • proj 1 - x 1 • proj 2 = 0 := by
    have hh := hgraph.fderiv_eq (𝕜 := ℂ)
    have hYZ' : HasFDerivAt (fun z : V 4 => z 1 * z 2)
        (x 1 • proj 2 + x 2 • proj 1) x := hYZ
    rw [hR.fderiv, hYZ'.fderiv] at hh
    rw [hh]
    module
  exact multiplier_coordinates _ _ _ _ _ _ _ _ _ _ _ hunit hFeq hReq

theorem critical_chart1 {E : V 4 → ℂ} {x : V 4} {R : V 3 → ℂ} (a b : ℕ)
    (he : DifferentiableAt ℂ E x) (hr : DifferentiableAt ℂ R (base1 E x))
    (hunit : partDeriv R (base1 E x) 1 ≠ 0)
    (hgraph : (fun z => R (base1 E z)) =ᶠ[𝓝 x] (fun z => z 1 * z 2))
    (hcrit : fderiv ℂ (restricted1 E a b) x = 0) :
    ∃ χ : ℂ,
      HX (x 0) (E x) = -χ * partDeriv R (base1 E x) 0 ∧
      HT (x 0) (E x) = -χ * partDeriv R (base1 E x) 1 ∧
      x 1 ^ a + x 2 ^ b = -χ * partDeriv R (base1 E x) 2 ∧
      (a : ℂ) * x 3 * x 1 ^ (a - 1) = χ * x 2 ∧
      (b : ℂ) * x 3 * x 2 ^ (b - 1) = χ * x 1 := by
  have hF := (H_deriv ((proj (0 : Fin 4)).hasFDerivAt (x := x)) he.hasFDerivAt).add
    (perturbation_deriv a b x)
  have hFeq : HT (x 0) (E x) • fderiv ℂ E x + HX (x 0) (E x) • proj 0 +
      (x 1 ^ a + x 2 ^ b) • proj 3 +
      ((a : ℂ) * x 3 * x 1 ^ (a - 1)) • proj 1 +
      ((b : ℂ) * x 3 * x 2 ^ (b - 1)) • proj 2 = 0 := by
    have hh : fderiv ℂ (restricted1 E a b) x = _ := hF.fderiv
    rw [hcrit] at hh
    rw [hh]
    simp only [perturbationD, ContinuousLinearMap.proj_apply]
    module
  have hR := root_base1_deriv he.hasFDerivAt hr
  have hYZ : HasFDerivAt (fun z : V 4 => z 1 * z 2)
      (x 1 • proj 2 + x 2 • proj 1) x :=
    ((proj (1 : Fin 4)).hasFDerivAt (x := x)).mul
      ((proj (2 : Fin 4)).hasFDerivAt (x := x))
  have hReq : partDeriv R (base1 E x) 1 • fderiv ℂ E x + partDeriv R (base1 E x) 0 • proj 0 +
      partDeriv R (base1 E x) 2 • proj 3 - x 2 • proj 1 - x 1 • proj 2 = 0 := by
    have hh := hgraph.fderiv_eq (𝕜 := ℂ)
    rw [hR.fderiv, hYZ.fderiv] at hh
    rw [hh]
    module
  obtain ⟨χ, ht, hx, hu, hy, hz⟩ :=
    multiplier_coordinates _ _ _ _ _ _ _ _ _ _ _ hunit hFeq hReq
  exact ⟨χ, hx, ht, hu, hy, hz⟩
end AmbientMultiplicity.ChartDifferential
namespace AmbientMultiplicity.Preparation
open Filter Topology
open CriticalEstimates ChartDifferential

 
def scaledCoeff0 (s : ℂ) (p : V 2) (j : Fin 4) : ℂ :=
  s ^ (4 - (j : ℕ)) * coeff0 p ⟨j, by omega⟩
def scaledCoeff1 (s : ℂ) (p : V 2) (j : Fin 4) : ℂ :=
  s ^ (4 - (j : ℕ)) * coeff1 p ⟨j, by omega⟩

lemma scaledCoeff0_analytic (s : ℂ) : AnalyticAt ℂ (scaledCoeff0 s) 0 := by
  apply AnalyticAt.pi
  intro j
  exact analyticAt_const.mul (((proj ⟨j, by omega⟩).analyticAt _).comp coeff0_spec.1)
lemma scaledCoeff1_analytic (s : ℂ) : AnalyticAt ℂ (scaledCoeff1 s) 0 := by
  apply AnalyticAt.pi
  intro j
  exact analyticAt_const.mul (((proj ⟨j, by omega⟩).analyticAt _).comp coeff1_spec.1)

lemma scaledCoeff0_zero (s : ℂ) : scaledCoeff0 s 0 = 0 := by
  ext j
  dsimp [scaledCoeff0]
  rw [coeff0_spec.2.1]
  change s ^ (4 - (j : ℕ)) * (graph0 0).coeff j = 0
  rw [graph0_specialization, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]
lemma scaledCoeff1_zero (s : ℂ) : scaledCoeff1 s 0 = 0 := by
  ext j
  dsimp [scaledCoeff1]
  rw [coeff1_spec.2.1]
  change s ^ (4 - (j : ℕ)) * (graph1 0).coeff j = 0
  rw [graph1_specialization, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]

def rescale3 (s : ℂ) : V 3 →L[ℂ] V 3 :=
  ContinuousLinearMap.pi ![proj 0, proj 1, s⁻¹ • proj 2]

lemma preparedRoot0_eq (s : ℂ) (hs : s ≠ 0) (z : V 3) :
    preparedRoot (scaledCoeff0 s) z = s ^ 4 * r0 (rescale3 s z) := by
  have hp : base3 (rescale3 s z) = base2 z := by ext i; fin_cases i <;> rfl
  simp only [preparedRoot, quartic, r0, root0, eval_rootPoly, hp, scaledCoeff0,
    Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, add_zero]
  have hu : rescale3 s z 2 = s⁻¹ * z 2 := rfl
  simp only [hu]
  norm_num only
  field_simp [hs]

lemma preparedRoot1_eq (s : ℂ) (hs : s ≠ 0) (z : V 3) :
    preparedRoot (scaledCoeff1 s) z = s ^ 4 * r1 (rescale3 s z) := by
  have hp : base3 (rescale3 s z) = base2 z := by ext i; fin_cases i <;> rfl
  simp only [preparedRoot, quartic, r1, root1, eval_rootPoly, hp, scaledCoeff1,
    Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, add_zero]
  have hu : rescale3 s z 2 = s⁻¹ * z 2 := rfl
  simp only [hu]
  norm_num only
  field_simp [hs]

lemma preparedRoot0_deriv (s : ℂ) (hs : s ≠ 0) :
    HasFDerivAt (preparedRoot (scaledCoeff0 s)) (s ^ 4 • proj 0) 0 := by
  have hr : HasFDerivAt r0 (proj 0) (rescale3 s 0) := by
    simpa using r0_deriv.hasFDerivAt
  convert! (hr.comp 0 (rescale3 s).hasFDerivAt).const_mul (s ^ 4) using 1
  · funext z
    exact preparedRoot0_eq s hs z

lemma preparedRoot1_deriv (s : ℂ) (hs : s ≠ 0) :
    HasFDerivAt (preparedRoot (scaledCoeff1 s)) (s ^ 4 • proj 1) 0 := by
  have hr : HasFDerivAt r1 (proj 1) (rescale3 s 0) := by
    simpa using r1_deriv.hasFDerivAt
  convert! (hr.comp 0 (rescale3 s).hasFDerivAt).const_mul (s ^ 4) using 1
  · funext z
    exact preparedRoot1_eq s hs z

lemma preparedRoot0_graph (s : ℂ) (hs : s ≠ 0) :
    ∀ᶠ x in 𝓝 (0 : V 4),
      preparedRoot (scaledCoeff0 s) (ChartDifferential.base0 (eliminated0 s) x) = x 1 * x 2 := by
  filter_upwards [chart0_on_hypersurface s hs, chart0_coordinates s] with x he hc
  have hrc : rescale3 s (ChartDifferential.base0 (eliminated0 s) x) =
      rescale s (chart0 s x) := by
    ext i
    fin_cases i
    · rfl
    · exact hc.1.symm
    · change s⁻¹ * x 3 = s⁻¹ * chart0 s x 4
      rw [hc.2.2.2.1]
  rw [preparedRoot0_eq s hs, hrc, ← he, hc.2.1, hc.2.2.1]

lemma preparedRoot1_graph (s : ℂ) (hs : s ≠ 0) :
    ∀ᶠ x in 𝓝 (0 : V 4),
      preparedRoot (scaledCoeff1 s) (ChartDifferential.base1 (eliminated1 s) x) = x 1 * x 2 := by
  filter_upwards [chart1_on_hypersurface s hs, chart1_coordinates s] with x he hc
  have hrc : rescale3 s (ChartDifferential.base1 (eliminated1 s) x) =
      rescale s (chart1 s x) := by
    ext i
    fin_cases i
    · exact hc.1.symm
    · rfl
    · change s⁻¹ * x 3 = s⁻¹ * chart1 s x 4
      rw [hc.2.2.2.1]
  rw [preparedRoot1_eq s hs, hrc, ← he, hc.2.1, hc.2.2.1]

lemma root_partial_eventually_ne {R : V 3 → ℂ} (hR : AnalyticAt ℂ R 0)
    (i : Fin 3) (hne : partDeriv R 0 i ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : V 3), partDeriv R z i ≠ 0 := by
  have hd : ContinuousAt (fderiv ℂ R) (0 : V 3) :=
    (hR.contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  exact (hd.clm_apply continuousAt_const).eventually_ne hne

def lift0 (s : ℂ) (x : V 4) : V 5 := ![eliminated0 s x, x 0, x 1, x 2, x 3]
def lift1 (s : ℂ) (x : V 4) : V 5 := ![x 0, eliminated1 s x, x 1, x 2, x 3]

lemma lift0_continuousAt (s : ℂ) : ContinuousAt (lift0 s) 0 := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact (eliminated0_analytic s).continuousAt
  all_goals exact (proj _).continuous.continuousAt
lemma lift1_continuousAt (s : ℂ) : ContinuousAt (lift1 s) 0 := by
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact (proj _).continuous.continuousAt
  · exact (eliminated1_analytic s).continuousAt
  all_goals exact (proj _).continuous.continuousAt

lemma lift0_zero (s : ℂ) : lift0 s 0 = 0 := by ext i; fin_cases i <;> simp [lift0, eliminated0_zero]
lemma lift1_zero (s : ℂ) : lift1 s 0 = 0 := by ext i; fin_cases i <;> simp [lift1, eliminated1_zero]

 

theorem f5_critical_vertical_zero (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : 11 ≤ a) (hb : 11 ≤ b) :
    ∀ᶠ x in 𝓝 (0 : V 4), fderiv ℂ (f5 s a b) x = 0 → x 1 = 0 ∧ x 2 = 0 := by
  have hA := scaledCoeff0_analytic s
  have hR := preparedRoot_analytic hA
  have hl : Tendsto (lift0 s) (𝓝 (0 : V 4)) (𝓝 0) := by
    simpa only [lift0_zero] using (lift0_continuousAt s).tendsto
  have ht : Tendsto (base0 (eliminated0 s)) (𝓝 (0 : V 4)) (𝓝 0) := by
    have hh := (base0_deriv (eliminated0_analytic s).differentiableAt.hasFDerivAt).continuousAt
    have heq : base0 (eliminated0 s) 0 = 0 := by ext i; fin_cases i <;> simp [base0, eliminated0_zero]
    simpa only [heq] using hh.tendsto
  have hu : ∀ᶠ z in 𝓝 (0 : V 3), partDeriv (preparedRoot (scaledCoeff0 s)) z 0 ≠ 0 := by
    apply root_partial_eventually_ne hR
    rw [partDeriv, (preparedRoot0_deriv s hs).fderiv]
    simpa using pow_ne_zero 4 hs
  have hv := critical_vertical_zero hA (scaledCoeff0_zero s) a b ha hb (1 : ℂ) one_ne_zero
  have hg0 : (fun x => preparedRoot (scaledCoeff0 s) (base0 (eliminated0 s) x)) =ᶠ[𝓝 (0 : V 4)] (fun x => x 1 * x 2) := preparedRoot0_graph s hs
  filter_upwards [(eliminated0_analytic s).eventually_analyticAt,
    ht.eventually hR.eventually_analyticAt, ht.eventually hu,
    hg0.eventuallyEq_nhds, hl.eventually hv] with x he hr hn hg hvx
  intro hc
  change fderiv ℂ (restricted0 (eliminated0 s) a b) x = 0 at hc
  obtain ⟨χ, hx, ht, hw, hy, hz⟩ :=
    critical_chart0 a b he.differentiableAt hr.differentiableAt hn hg hc
  apply hvx
  unfold ConstrainedCritical
  have hlb : base5 (lift0 s x) = base0 (eliminated0 s) x := by ext i; fin_cases i <;> rfl
  rw [hlb]
  change x 1 * x 2 = preparedRoot (scaledCoeff0 s) (base0 (eliminated0 s) x) ∧ _
  refine ⟨hg.self_of_nhds.symm, χ, hx, ht, ?_, ?_, ?_⟩
  · simpa [lift0, lift1, partDeriv] using hw
  · simpa [lift0, lift1, partDeriv] using hy
  · simpa [lift0, lift1, partDeriv] using hz

theorem f4_critical_vertical_zero (s : ℂ) (hs : s ≠ 0) (a b : ℕ)
    (ha : 11 ≤ a) (hb : 11 ≤ b) :
    ∀ᶠ x in 𝓝 (0 : V 4), fderiv ℂ (f4 s a b) x = 0 → x 1 = 0 ∧ x 2 = 0 := by
  have hA := scaledCoeff1_analytic s
  have hR := preparedRoot_analytic hA
  have hl : Tendsto (lift1 s) (𝓝 (0 : V 4)) (𝓝 0) := by
    simpa only [lift1_zero] using (lift1_continuousAt s).tendsto
  have ht : Tendsto (base1 (eliminated1 s)) (𝓝 (0 : V 4)) (𝓝 0) := by
    have hh := (base1_deriv (eliminated1_analytic s).differentiableAt.hasFDerivAt).continuousAt
    have heq : base1 (eliminated1 s) 0 = 0 := by ext i; fin_cases i <;> simp [base1, eliminated1_zero]
    simpa only [heq] using hh.tendsto
  have hu : ∀ᶠ z in 𝓝 (0 : V 3), partDeriv (preparedRoot (scaledCoeff1 s)) z 1 ≠ 0 := by
    apply root_partial_eventually_ne hR
    rw [partDeriv, (preparedRoot1_deriv s hs).fderiv]
    simpa using pow_ne_zero 4 hs
  have hv := critical_vertical_zero hA (scaledCoeff1_zero s) a b ha hb (1 : ℂ) one_ne_zero
  have hg0 : (fun x => preparedRoot (scaledCoeff1 s) (base1 (eliminated1 s) x)) =ᶠ[𝓝 (0 : V 4)] (fun x => x 1 * x 2) := preparedRoot1_graph s hs
  filter_upwards [(eliminated1_analytic s).eventually_analyticAt,
    ht.eventually hR.eventually_analyticAt, ht.eventually hu,
    hg0.eventuallyEq_nhds, hl.eventually hv] with x he hr hn hg hvx
  intro hc
  change fderiv ℂ (restricted1 (eliminated1 s) a b) x = 0 at hc
  obtain ⟨χ, hx, ht, hw, hy, hz⟩ :=
    critical_chart1 a b he.differentiableAt hr.differentiableAt hn hg hc
  apply hvx
  unfold ConstrainedCritical
  have hlb : base5 (lift1 s x) = base1 (eliminated1 s) x := by ext i; fin_cases i <;> rfl
  rw [hlb]
  change x 1 * x 2 = preparedRoot (scaledCoeff1 s) (base1 (eliminated1 s) x) ∧ _
  refine ⟨hg.self_of_nhds.symm, χ, hx, ht, ?_, ?_, ?_⟩
  · simpa [lift0, lift1, partDeriv] using hw
  · simpa [lift0, lift1, partDeriv] using hy
  · simpa [lift0, lift1, partDeriv] using hz

end AmbientMultiplicity.Preparation

end

end OAI
