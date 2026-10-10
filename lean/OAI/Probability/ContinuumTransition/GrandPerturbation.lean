import OAI.Probability.ContinuumTransition.GrandInteraction

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grand_log_perturbation_bound (F₀ F₁ H : ConfigFamily) {D : Set Space}
    (hD : MeasurableSet D) (h₀ : GrandFinite F₀ D) (h₁ : GrandFinite F₁ D) (hH : GrandFinite H D)
    (hZ₁ : 0 < grandIntegral F₁ D)
    (hF₁ : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F₁ ι x)
    (B : ConfigFamily)
    (hrel : ∀ (ι : Type) [Fintype ι] (x : ι → Space),
      F₀ ι x = F₁ ι x*Real.exp (-B ι x))
    (hHB : ∀ (ι : Type) [Fintype ι] (x : ι → Space), H ι x = F₁ ι x*B ι x) :
    Real.log (grandIntegral F₁ D)-Real.log (grandIntegral F₀ D) ≤
      grandIntegral H D/grandIntegral F₁ D := by
  let a := grandIntegral H D/grandIntegral F₁ D
  let G : ConfigFamily := fun ι _ x => Real.exp (-a)*((1+a)*F₁ ι x+(-1)*H ι x)
  have hG : GrandFinite G D := ((h₁.const_mul (1+a)).add (hH.const_mul (-1))).const_mul _
  have hpoint (ι : Type) [Fintype ι] (x : ι → Space) : G ι x ≤ F₀ ι x := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a-B ι x))
      (mul_nonneg (Real.exp_pos (-a)).le (hF₁ ι x))
    rw [hrel ι x]
    dsimp only [G]
    rw [hHB ι x]
    have he : Real.exp (-a)*Real.exp (a-B ι x) = Real.exp (-B ι x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (Real.exp (-a)*F₁ ι x)*(a-B ι x+1) := by ring
      _ ≤ (Real.exp (-a)*F₁ ι x)*Real.exp (a-B ι x) := hh
      _ = F₁ ι x*(Real.exp (-a)*Real.exp (a-B ι x)) := by ring
      _ = _ := by rw [he]
  have hh := grandIntegral_mono G F₀ hD (fun n => hG.integrable (Fin n))
    (fun n => h₀.integrable (Fin n)) hG.summable h₀.summable (fun n x _ => hpoint (Fin n) x)
  have he : grandIntegral G D = Real.exp (-a)*grandIntegral F₁ D := by
    rw [grandIntegral_const_mul, grandIntegral_add _ _ D
      (fun n => (h₁.const_mul _).integrable (Fin n))
      (fun n => (hH.const_mul _).integrable (Fin n))
      (h₁.const_mul _).summable (hH.const_mul _).summable,
      grandIntegral_const_mul, grandIntegral_const_mul]
    dsimp only [a]
    field_simp
    ring
  rw [he] at hh
  have hl := Real.log_le_log (mul_pos (Real.exp_pos (-a)) hZ₁) hh
  rw [Real.log_mul (Real.exp_pos (-a)).ne' hZ₁.ne', Real.log_exp] at hl
  change _ ≤ a
  linarith only [hl]

end ContinuumTemperature
end

end OAI
