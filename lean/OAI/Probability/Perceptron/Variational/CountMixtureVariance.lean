import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace SphericalPerceptronFreeEnergy

lemma memLp_prod_of_conditional_square_function {X Y : Type}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X×Y → ℝ} {G A : X → ℝ} (hF : Measurable F) (hG : MemLp G 2 μ)
    (hA : Integrable A μ) (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hb : ∀ x, (∫ y, (F (x,y)-G x)^2 ∂ν) ≤ A x) : MemLp F 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hF.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => (hs x).integrable_sq),?_⟩
  have hi : Integrable (fun x => 2*A x+2*(G x)^2) μ :=
    (hA.const_mul 2).add (hG.integrable_sq.const_mul 2)
  apply hi.mono' (hF.pow_const 2).aestronglyMeasurable.norm.integral_prod_right'
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs,abs_sq]
    rw [abs_of_nonneg (integral_nonneg (fun y : Y => sq_nonneg (F (x,y))))]
    have hi1 : Integrable (fun y => (F (x,y)-G x)^2) ν :=
      ((hs x).sub (memLp_const (G x))).integrable_sq
    calc
      _ ≤ ∫ y, 2*(F (x,y)-G x)^2+2*(G x)^2 ∂ν := by
        apply integral_mono (hs x).integrable_sq ((hi1.const_mul 2).add (integrable_const _))
        intro y
        dsimp only [Pi.add_apply]
        nlinarith [sq_nonneg (F (x,y)-2*G x)]
      _ = 2*(∫ y, (F (x,y)-G x)^2 ∂ν)+2*(G x)^2 := by
        rw [integral_add (hi1.const_mul 2) (integrable_const _),integral_const_mul]
        simp
      _ ≤ _ := by linarith [hb x]

lemma variance_prod_le_integral {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : X × Y → ℝ} (hp : MemLp F 2 (μ.prod ν))
    (hs : ∀ x, MemLp (fun y => F (x,y)) 2 ν)
    (hh : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 μ) {A : X → ℝ} {B : ℝ}
    (hAi : Integrable A μ) (hA : ∀ x, variance (fun y => F (x,y)) ν ≤ A x)
    (hB : variance (fun x => ∫ y, F (x,y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ (∫ x, A x ∂μ)+B := by
  have hi : (∫ x, ∫ y, F (x,y)^2 ∂ν ∂μ) ≤ (∫ x, A x ∂μ)+∫ x, (∫ y, F (x,y) ∂ν)^2 ∂μ := by
    calc
      _ ≤ ∫ x, (A x+(∫ y, F (x,y) ∂ν)^2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left (hAi.add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply,Pi.add_apply] using sub_le_iff_le_add.mp hv
      _ = _ := integral_add hAi hh.integrable_sq
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,integral_prod _ (hp.integrable (by norm_num))]
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
