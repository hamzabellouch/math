import OAI.Dynamics.EntropyCounterexample.Clock
import OAI.Dynamics.EntropyCounterexample.ReadoutCover
import OAI.Dynamics.EntropyCounterexample.SpherePerturbation

namespace OAI

noncomputable section

open scoped OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

abbrev Sphere := OnePoint ℂ
abbrev RawManifold := AddCircle (100 : ℝ) × (Sphere × (Fin 3 → Sphere))

structure SphereData where
  gate : Sphere → ℝ
  cutoff : Sphere → ℝ
  saturation : Sphere → ℂ
  gain : ℝ → ℝ
  L : ℝ

def phase : Sphere → ℂ := OnePoint.rec 0 (fun z : ℂ => z / (‖z‖ : ℂ))

@[simp] theorem phase_infty : phase ∞ = 0 := rfl
@[simp] theorem phase_coe (z : ℂ) : phase (z : Sphere) = z / (‖z‖ : ℂ) := rfl
@[simp] theorem phase_zero : phase ((0 : ℂ) : Sphere) = 0 := by simp

def prediction (D : SphereData) (x : ℝ × Sphere) : ℝ × Sphere :=
  (x.1 + Clock.increment x.1 (D.gate x.2), perturbedSquare 0 x.2)

def predictedClock (D : SphereData) (m : ℕ) (t : ℝ) (z : Sphere) : ℝ :=
  ((prediction D)^[m] (t, z)).1

def inputTerm (D : SphereData) (i : Fin 3) (n : ℕ) (t : ℝ) (z : Sphere) : ℂ :=
  (((D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z : ℝ) : ℂ) *
    phase z ^ (2 ^ (n + 2))

def baseInput (D : SphereData) (i : Fin 3) (t : ℝ) (z : Sphere) : ℂ :=
  ((preparationCoeff t / 10 : ℝ) : ℂ) * ∑' n : ℕ, inputTerm D i n t z

def input (D : SphereData) (i : Fin 3) (t : AddCircle (100 : ℝ)) (z : Sphere) : ℂ :=
  AddCircle.liftIco 100 0 (fun s => baseInput D i s z) t

def periodicReadout (i : Fin 3) : AddCircle (100 : ℝ) → ℝ :=
  AddCircle.liftIco 100 0 (readoutCoeff i)

def periodicGain (D : SphereData) : AddCircle (100 : ℝ) → ℝ :=
  AddCircle.liftIco 100 0 D.gain

def clockIncrement (D : SphereData) (t : AddCircle (100 : ℝ)) (z : Sphere) : ℝ :=
  AddCircle.liftIco 100 0 (fun s => Clock.increment s (D.gate z)) t

def readout (D : SphereData) (t : AddCircle (100 : ℝ)) (v : Fin 3 → Sphere) : ℂ :=
  20 * ∑ i : Fin 3, (periodicReadout i t : ℂ) * D.saturation (v i)

def rawMap (D : SphereData) (x : RawManifold) : RawManifold :=
  (x.1 + (clockIncrement D x.1 x.2.1 : ℝ),
    perturbedSquare (readout D x.1 x.2.2) x.2.1,
    fun i => (((periodicGain D x.1 : ℂ) * D.saturation (x.2.2 i) +
      input D i x.1 x.2.1 : ℂ) : Sphere))

@[simp] theorem rawMap_main_infty (D : SphereData)
    (t : AddCircle (100 : ℝ)) (v : Fin 3 → Sphere) :
    (rawMap D (t, ∞, v)).2.1 = ∞ := rfl

theorem rawMap_register_ne_infty (D : SphereData) (x : RawManifold) (i : Fin 3) :
    (rawMap D x).2.2 i ≠ ∞ := OnePoint.coe_ne_infty _

theorem rawMap_not_surjective (D : SphereData) : ¬ Function.Surjective (rawMap D) := by
  intro h
  obtain ⟨x, hx⟩ := h (0, ∞, fun _ => ∞)
  have heq := congrArg (fun y : RawManifold => y.2.2 (0 : Fin 3)) hx
  exact rawMap_register_ne_infty D x 0 heq

theorem rawMap_not_bijective (D : SphereData) : ¬ Function.Bijective (rawMap D) :=
  fun h => rawMap_not_surjective D h.2

@[simp] theorem inputTerm_infty (D : SphereData) (i : Fin 3) (n : ℕ) (t : ℝ) :
    inputTerm D i n t ∞ = 0 := by simp [inputTerm]

@[simp] theorem inputTerm_zero (D : SphereData) (i : Fin 3) (n : ℕ) (t : ℝ) :
    inputTerm D i n t ((0 : ℂ) : Sphere) = 0 := by simp [inputTerm]

@[simp] theorem baseInput_infty (D : SphereData) (i : Fin 3) (t : ℝ) :
    baseInput D i t ∞ = 0 := by simp [baseInput]

@[simp] theorem baseInput_zero (D : SphereData) (i : Fin 3) (t : ℝ) :
    baseInput D i t ((0 : ℂ) : Sphere) = 0 := by simp [baseInput]

@[simp] theorem input_infty (D : SphereData) (i : Fin 3) (t : AddCircle (100 : ℝ)) :
    input D i t ∞ = 0 := by simp [input, AddCircle.liftIco]

@[simp] theorem input_zero (D : SphereData) (i : Fin 3) (t : AddCircle (100 : ℝ)) :
    input D i t ((0 : ℂ) : Sphere) = 0 := by simp [input, AddCircle.liftIco]

theorem norm_phase_le_one (z : Sphere) : ‖phase z‖ ≤ 1 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
      by_cases hz : z = 0
      · simp [hz]
      · simp [phase_coe, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem norm_inputTerm_le (D : SphereData) (hL : 0 ≤ D.L)
    (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) (n : ℕ) (t : ℝ) (z : Sphere) :
    ‖inputTerm D i n t z‖ ≤ (D.L⁻¹) ^ n := by
  have hpow : 0 ≤ (D.L⁻¹) ^ n := pow_nonneg (inv_nonneg.mpr hL) n
  have hβ0 := readoutCoeff_nonneg i (predictedClock D (n + 1) t z)
  have hβ1 := readoutCoeff_le_one i (predictedClock D (n + 1) t z)
  have hcoef0 : 0 ≤ (D.L⁻¹) ^ n *
      readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z :=
    mul_nonneg (mul_nonneg hpow hβ0) (hχ0 z)
  have hcoef1 : (D.L⁻¹) ^ n *
      readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z ≤ (D.L⁻¹) ^ n := by
    calc
      _ ≤ (D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) t z) :=
        mul_le_of_le_one_right (mul_nonneg hpow hβ0) (hχ1 z)
      _ ≤ (D.L⁻¹) ^ n := mul_le_of_le_one_right hpow hβ1
  calc
    ‖inputTerm D i n t z‖ = ((D.L⁻¹) ^ n *
      readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z) *
      ‖phase z‖ ^ (2 ^ (n + 2)) := by
        simp only [inputTerm, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hL),
          abs_of_nonneg hβ0, abs_of_nonneg (hχ0 z)]
    _ ≤ (D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) t z) * D.cutoff z :=
      mul_le_of_le_one_right hcoef0
        (pow_le_one₀ (norm_nonneg _) (norm_phase_le_one z))
    _ ≤ (D.L⁻¹) ^ n := hcoef1

theorem summable_norm_inputTerm (D : SphereData) (hL : 1 < D.L)
    (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) (t : ℝ) (z : Sphere) :
    Summable (fun n : ℕ => ‖inputTerm D i n t z‖) := by
  have hL0 : 0 < D.L := by linarith
  have hInv : D.L⁻¹ < 1 := (inv_lt_one₀ hL0).2 hL
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_inputTerm_le D hL0.le hχ0 hχ1 i n t z)
    (summable_geometric_of_lt_one (inv_nonneg.mpr hL0.le) hInv)

theorem summable_inputTerm (D : SphereData) (hL : 1 < D.L)
    (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) (t : ℝ) (z : Sphere) : Summable (fun n : ℕ => inputTerm D i n t z) :=
  (summable_norm_inputTerm D hL hχ0 hχ1 i t z).of_norm

theorem norm_baseInput_le (D : SphereData) (hL : 1 < D.L)
    (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) (t : ℝ) (z : Sphere) :
    ‖baseInput D i t z‖ ≤ D.L / (10 * (D.L - 1)) := by
  have hL0 : 0 < D.L := by linarith
  have hInv : D.L⁻¹ < 1 := (inv_lt_one₀ hL0).2 hL
  have hgeom := summable_geometric_of_lt_one (inv_nonneg.mpr hL0.le) hInv
  have hnorm := summable_norm_inputTerm D hL hχ0 hχ1 i t z
  have hsum : ‖∑' n : ℕ, inputTerm D i n t z‖ ≤ (1 - D.L⁻¹)⁻¹ := by
    calc
      _ ≤ ∑' n : ℕ, ‖inputTerm D i n t z‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : ℕ, (D.L⁻¹) ^ n :=
        hnorm.tsum_le_tsum (fun n => norm_inputTerm_le D hL0.le hχ0 hχ1 i n t z) hgeom
      _ = (1 - D.L⁻¹)⁻¹ := tsum_geometric_of_lt_one (inv_nonneg.mpr hL0.le) hInv
  have hα0 : 0 ≤ preparationCoeff t / 10 := by
    exact div_nonneg (preparationCoeff_nonneg t) (by norm_num)
  have hα1 : preparationCoeff t / 10 ≤ 1 / 10 := by
    exact div_le_div_of_nonneg_right (preparationCoeff_le_one t) (by norm_num)
  calc
    ‖baseInput D i t z‖ = (preparationCoeff t / 10) *
        ‖∑' n : ℕ, inputTerm D i n t z‖ := by
      rw [baseInput, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα0]
    _ ≤ (1 / 10) * (1 - D.L⁻¹)⁻¹ :=
      mul_le_mul hα1 hsum (norm_nonneg _) (by norm_num)
    _ = D.L / (10 * (D.L - 1)) := by
      have hL1 : D.L - 1 ≠ 0 := by linarith
      field_simp

end Problem340.Construction

end

end OAI
