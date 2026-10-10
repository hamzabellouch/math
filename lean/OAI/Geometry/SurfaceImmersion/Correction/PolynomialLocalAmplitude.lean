import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAmplitudeBounds
import OAI.Geometry.Immersion.ClosedSurface.LocalMean

namespace OAI

/-! Polynomial square-root amplitudes for the actual local metric data. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes RootMean WeightedEstimates FiniteMean

def coefficientBudget (m : ℕ) (B : ℝ) : ℝ := 2^m*B*(m.factorial : ℝ)*B^m

lemma coefficientBudget_polynomial (m : ℕ) : HasPolynomialBound (coefficientBudget m) := by
  unfold coefficientBudget
  repeat first
    | exact polynomialBound_id
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

variable {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
  {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

lemma inputFactor_le_coefficientBudget (d : Budgets U V s F ψ Q χ e)
    (m : ℕ) {B : ℝ} (hB : 1 ≤ B) (hi : d.inv m ≤ B) (hf : d.forms m ≤ B) :
    inputFactor d m ≤ coefficientBudget m B := by
  have hI := d.inv_pos m
  have hF := d.forms_pos m
  unfold inputFactor coefficientBudget
  gcongr

theorem polynomial_local_amplitude_bounds (m : ℕ) :
    ∃ p : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∀ {U V : Set Base} {s r ρ R : ℝ} {reference : Base → Tensor}
      {F : RField 4} {ψ : Base → ℝ} {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base},
      ∀ (_h : LocalBounds U V s r ρ R reference F ψ Q χ e)
        (d : Budgets U V s F ψ Q χ e),
      0 < s → s ≤ 1 → 0 < ρ → ∀ B : ℝ, 1 ≤ B → ρ⁻¹ ≤ B →
      d.inv m ≤ B → d.forms m ≤ B → d.psi m ≤ B →
    ∀ (A A' : Base → Tensor) (D : ℝ), 0 ≤ D →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ A' U →
      InTrialBall U reference r A → InTrialBall U reference r A' →
      WeightedBound U s m B A → WeightedBound U s m B A' →
      WeightedBound U s m D (A-A') →
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A)) ∧
      WeightedBound V s m (C*B^p) (phaseAmplitude ψ (coefficient Q e A')) ∧
      WeightedBound V s m (C*B^p*D)
        (fun x => phaseAmplitude ψ (coefficient Q e A) x-phaseAmplitude ψ (coefficient Q e A') x) := by
  obtain ⟨k,C₀,hC₀,hamp⟩ := polynomial_phaseAmplitude_bounds (E := Base) m
  let S := fun B : ℝ => 1+B+coefficientBudget m B*B
  have hSp : HasPolynomialBound S :=
    ((polynomialBound_const zero_le_one).add polynomialBound_id).add
      ((coefficientBudget_polynomial m).mul polynomialBound_id)
  have hpoly : HasPolynomialBound (fun B => C₀*(S B)^k*(1+coefficientBudget m B)) :=
    ((polynomialBound_const (zero_le_one.trans hC₀)).mul (hSp.pow k)).mul
      ((polynomialBound_const zero_le_one).add (coefficientBudget_polynomial m))
  obtain ⟨p,C,hC,hpoly⟩ := hpoly
  refine ⟨p,C,hC,?_⟩
  intro U V s r ρ R reference F ψ Q χ e h d hs hs1 hρ B hB hρB hi hf hψ A A' D hD hA hA' hball hball' hbA hbA' hbD
  have hB0 := zero_le_one.trans hB
  have hJ : 0 ≤ coefficientBudget m B := by unfold coefficientBudget; positivity
  have hS : 1 ≤ S B ∧ B ≤ S B ∧ coefficientBudget m B*B ≤ S B := by
    dsimp [S]
    have hh : 0 ≤ coefficientBudget m B*B := mul_nonneg hJ hB0
    constructor
    · linarith
    constructor <;> linarith
  have hfactor := inputFactor_le_coefficientBudget d m hB hi hf
  have hcoeff (T : Base → Tensor) (hT : ContDiffOn ℝ ∞ T U)
      (hbT : WeightedBound U s m B T) : WeightedBound V s m (S B) (coefficient Q e T) := by
    have hh := weighted_coefficient h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
      (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hB0 h.smoothQ h.smoothInv
      h.invInto hT (d.inv_bound m) (d.forms_bound m) hbT
    exact hh.mono_const ((mul_le_mul_of_nonneg_right hfactor hB0).trans hS.2.2)
  have hdiff := weighted_coefficient_difference h.openU.uniqueDiffOn h.domain.isOpen.uniqueDiffOn hs hs1
    (d.inv_pos m) (zero_le_one.trans (d.forms_pos m)) hD h.smoothQ h.smoothInv
    h.invInto hA hA' (d.inv_bound m) (d.forms_bound m) hbD
  have hdiff' : WeightedBound V s m (coefficientBudget m B*D)
      ((coefficient Q e A)-(coefficient Q e A')) :=
    hdiff.mono_const (mul_le_mul_of_nonneg_right hfactor hD)
  have hpos (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, 0 < coefficient Q e T x :=
    fun x hx => hρ.trans_le (coefficient_trial_range h.invInto h.margin ht hx).1
  have hinv (T : Base → Tensor) (ht : InTrialBall U reference r T) :
      ∀ x ∈ V, (coefficient Q e T x)⁻¹ ≤ S B := by
    intro x hx
    exact ((inv_le_inv₀ (hpos T ht x hx) hρ).mpr
      (coefficient_trial_range h.invInto h.margin ht hx).1).trans (hρB.trans hS.2.1)
  obtain ⟨ha,ha',hd⟩ := hamp h.domain.isOpen.uniqueDiffOn hs hS.1 (mul_nonneg hJ hD)
    h.smoothPsi (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA)
    (contDiffOn_coefficient h.smoothQ h.smoothInv h.invInto hA')
    (hpos A hball) (hpos A' hball') (hinv A hball) (hinv A' hball')
    ((d.psi_bound m).mono_const (hψ.trans hS.2.1)) (hcoeff A hA hbA) (hcoeff A' hA' hbA') hdiff'
  have hsize := (hpoly B hB).2
  have hbase : C₀*(S B)^k ≤ C*B^p := by
    calc
      _ ≤ C₀*(S B)^k*(1+coefficientBudget m B) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      _ ≤ _ := hsize
  have hdiffsize : C₀*(S B)^k*(coefficientBudget m B*D) ≤ C*B^p*D := by
    calc
      _ ≤ (C₀*(S B)^k*(1+coefficientBudget m B))*D := by
        have hz : 0 ≤ C₀*(S B)^k := by positivity
        nlinarith [mul_nonneg hz hD]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsize hD
  exact ⟨ha.mono_const hbase,ha'.mono_const hbase,hd.mono_const hdiffsize⟩

end ClosedSurfaceR4.PhaseMean

end

end OAI
