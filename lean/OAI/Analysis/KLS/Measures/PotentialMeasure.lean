import OAI.Analysis.KLS.Sobolev.TestFunctions
import Mathlib.MeasureTheory.Measure.Tilted

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace LeanBlast.KLS

variable {n : ℕ}

def potentialPartition (V : Space n → ℝ) : ℝ :=
  ∫ x, Real.exp (-V x)

def potentialDensity (V : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (-V x) / potentialPartition V

def potentialMeasure (V : Space n → ℝ) : Measure (Space n) :=
  volume.tilted (fun x => -V x)

theorem potentialMeasure_eq_densityMeasure (V : Space n → ℝ) :
    potentialMeasure V = densityMeasure (potentialDensity V) := rfl

theorem potentialPartition_pos {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) : 0 < potentialPartition V :=
  integral_exp_pos hV

theorem potentialDensity_pos {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) (x : Space n) :
    0 < potentialDensity V x := div_pos (Real.exp_pos _) (potentialPartition_pos hV)

theorem isProbabilityMeasure_potentialMeasure {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) :
    IsProbabilityMeasure (potentialMeasure V) :=
  isProbabilityMeasure_tilted hV

theorem integral_potentialMeasure (V g : Space n → ℝ) :
    (∫ x, g x ∂potentialMeasure V) =
      (∫ x, Real.exp (-V x) * g x) / potentialPartition V := by
  rw [potentialMeasure, integral_tilted]
  simp only [smul_eq_mul]
  simp_rw [div_mul_eq_mul_div]
  simpa only [div_eq_mul_inv, potentialPartition] using
    integral_mul_const (potentialPartition V)⁻¹ (fun x => Real.exp (-V x) * g x)

theorem integrable_potentialMeasure_iff {V : Space n → ℝ}
    (hV : Integrable (fun x => Real.exp (-V x))) (g : Space n → ℝ) :
    Integrable g (potentialMeasure V) ↔ Integrable (fun x => Real.exp (-V x) * g x) := by
  simpa only [potentialMeasure, smul_eq_mul] using integrable_tilted_iff hV g

theorem potentialMeasure_of_normalized {V : Space n → ℝ}
    (hV : potentialPartition V = 1) :
    potentialMeasure V = densityMeasure (fun x => Real.exp (-V x)) := by
  rw [potentialMeasure_eq_densityMeasure]
  congr 1
  funext x
  simp only [potentialDensity, hV, div_one]

theorem variance_eq_integral_sq_sub_sq (μ : Measure (Space n)) [IsProbabilityMeasure μ]
    {h : Space n → ℝ} (hh : Integrable h μ) (hh2 : Integrable (fun x => (h x) ^ 2) μ) :
    variance μ h = (∫ x, (h x) ^ 2 ∂μ) - (∫ x, h x ∂μ) ^ 2 := by
  unfold variance expectation
  have heq : (fun x => (h x - ∫ y, h y ∂μ) ^ 2) =
      fun x => ((h x) ^ 2 - (2 * ∫ y, h y ∂μ) * h x) + (∫ y, h y ∂μ) ^ 2 := by
    funext x
    ring
  rw [heq]
  rw [integral_add (f := fun x => h x ^ 2 - (2 * ∫ y, h y ∂μ) * h x)
    (g := fun _ => (∫ y, h y ∂μ) ^ 2)
    (hh2.sub (hh.const_mul _)) (integrable_const _)]
  rw [integral_sub (f := fun x => h x ^ 2) (g := fun x => (2 * ∫ y, h y ∂μ) * h x)
    hh2 (hh.const_mul _), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  ring

end LeanBlast.KLS

end

end OAI
