import OAI.Probability.ContinuumTransition.GrandFinite

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem GrandFinite.of_le {F G : ConfigFamily} {D : Set Space} (hG : GrandFinite G D)
    (hm : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (h0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFG : ∀ (ι : Type) [Fintype ι] (x : ι → Space), F ι x ≤ G ι x) : GrandFinite F D := by
  have hi (ι : Type) [Fintype ι] : IntegrableOn (F ι) {x | ∀ i, x i ∈ D} := by
    apply (hG.integrable ι).mono' (hm ι).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h0 ι x)] using hFG ι x)
  refine ⟨fun ι _ => hi ι, ?_⟩
  apply Summable.of_nonneg_of_le (familyTerm_nonneg F D h0) _ hG.summable
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact integral_mono (hi (Fin n)) (hG.integrable (Fin n)) (hFG (Fin n))

theorem square_product_le_exponentials {c : ℝ} (hc : 0 < c) (x y : ℝ) :
    x*y ≤ (Real.exp (c*x^2)+Real.exp (c*y^2))/(2*c) := by
  have hx := Real.add_one_le_exp (c*x^2)
  have hy := Real.add_one_le_exp (c*y^2)
  apply (le_div_iff₀ (by positivity : 0 < 2*c)).2
  nlinarith [mul_nonneg hc.le (sq_nonneg (x-y))]

noncomputable def occupationPairFamily (F : ConfigFamily) (C D : Set Space) : ConfigFamily :=
  fun ι _ x => F ι x*(occupation C x*occupation D x)

theorem occupationPairFamily_nonneg (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C D : Set Space) (ι : Type) [Fintype ι] (x : ι → Space) :
    0 ≤ occupationPairFamily F C D ι x :=
  mul_nonneg (hF ι x) (mul_nonneg (occupation_nonneg C x) (occupation_nonneg D x))

theorem occupationPairFamily_le (F : ConfigFamily)
    (hF : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (C D : Set Space) {c : ℝ} (hc : 0 < c) (ι : Type) [Fintype ι] (x : ι → Space) :
    occupationPairFamily F C D ι x ≤
      (2*c)⁻¹*momentFamily F C c ι x+(2*c)⁻¹*momentFamily F D c ι x := by
  have hh := mul_le_mul_of_nonneg_left (square_product_le_exponentials hc (occupation C x) (occupation D x)) (hF ι x)
  simpa only [occupationPairFamily, momentFamily, mul_add, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh

theorem GrandFinite.occupationPair {F : ConfigFamily} {D C₁ C₂ : Set Space}
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFmeas : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hC₁ : MeasurableSet C₁) (hC₂ : MeasurableSet C₂) {c : ℝ} (hc : 0 < c)
    (h₁ : GrandFinite (momentFamily F C₁ c) D) (h₂ : GrandFinite (momentFamily F C₂ c) D) :
    GrandFinite (occupationPairFamily F C₁ C₂) D := by
  apply GrandFinite.of_le ((h₁.const_mul (2*c)⁻¹).add (h₂.const_mul (2*c)⁻¹))
    (fun ι _ => (hFmeas ι).mul ((measurable_occupation hC₁).mul (measurable_occupation hC₂)))
    (occupationPairFamily_nonneg F hF0 C₁ C₂)
  exact occupationPairFamily_le F hF0 C₁ C₂ hc

theorem grand_pair_moment_le {F : ConfigFamily} {D C₁ C₂ : Set Space}
    (hD : MeasurableSet D)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hFmeas : ∀ (ι : Type) [Fintype ι], Measurable (F ι))
    (hC₁ : MeasurableSet C₁) (hC₂ : MeasurableSet C₂) {c M : ℝ} (hc : 0 < c)
    (h₁ : GrandFinite (momentFamily F C₁ c) D) (h₂ : GrandFinite (momentFamily F C₂ c) D)
    (hZ : 0 < grandIntegral F D)
    (hb₁ : grandIntegral (momentFamily F C₁ c) D/grandIntegral F D ≤ M)
    (hb₂ : grandIntegral (momentFamily F C₂ c) D/grandIntegral F D ≤ M) :
    grandIntegral (occupationPairFamily F C₁ C₂) D/grandIntegral F D ≤ M/c := by
  let G : ConfigFamily := fun ι _ x => (2*c)⁻¹*momentFamily F C₁ c ι x+(2*c)⁻¹*momentFamily F C₂ c ι x
  have hG : GrandFinite G D := (h₁.const_mul _).add (h₂.const_mul _)
  have hp := GrandFinite.occupationPair hF0 hFmeas hC₁ hC₂ hc h₁ h₂
  have hh := grandIntegral_mono (occupationPairFamily F C₁ C₂) G hD
    (fun n => hp.integrable (Fin n)) (fun n => hG.integrable (Fin n)) hp.summable hG.summable
    (fun n x _ => occupationPairFamily_le F hF0 C₁ C₂ hc (Fin n) x)
  have he : grandIntegral G D = (2*c)⁻¹*grandIntegral (momentFamily F C₁ c) D+
      (2*c)⁻¹*grandIntegral (momentFamily F C₂ c) D := by
    rw [grandIntegral_add _ _ D (fun _ => (h₁.const_mul _).integrable _)
      (fun _ => (h₂.const_mul _).integrable _) (h₁.const_mul _).summable (h₂.const_mul _).summable,
      grandIntegral_const_mul, grandIntegral_const_mul]
  rw [he] at hh
  apply (div_le_div_of_nonneg_right hh hZ.le).trans
  rw [add_div, mul_div_assoc, mul_div_assoc]
  have hci : 0 ≤ (2*c)⁻¹ := by positivity
  have hb := add_le_add (mul_le_mul_of_nonneg_left hb₁ hci) (mul_le_mul_of_nonneg_left hb₂ hci)
  apply hb.trans_eq
  field_simp
  ring

end ContinuumTemperature
end

end OAI
