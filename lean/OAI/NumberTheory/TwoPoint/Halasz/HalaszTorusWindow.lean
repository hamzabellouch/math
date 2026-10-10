import OAI.NumberTheory.TwoPoint.Halasz.HalaszCircleWindow
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusTranslation

namespace OAI

/-! The product localization window and its exact volume on the finite
coefficient torus. -/
namespace TwoPointCorrelations

open MeasureTheory Finset Set Metric
open scoped Classical ComplexConjugate

noncomputable def halaszTorusWindow {k : ℕ} (δ : Fin k → ℝ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  (Set.univ.pi (fun j => closedBall 0 (δ j))).indicator (fun _ => 1) α

lemma halasz_torus_window_measurable_set {k : ℕ} (δ : Fin k → ℝ) :
    MeasurableSet (Set.univ.pi (fun j => closedBall (0:AddCircle (1:ℝ)) (δ j))) := by
  exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_closedBall)

lemma halasz_torus_window_product {k : ℕ} (δ : Fin k → ℝ)
    (α : Fin k → AddCircle (1:ℝ)) :
    halaszTorusWindow δ α=∏ j,halaszCircleWindow (δ j) (α j) := by
  simp [halaszTorusWindow,halaszCircleWindow,Set.indicator,Finset.prod_boole]

lemma halasz_torus_window_memLp {k : ℕ} (δ : Fin k → ℝ) :
    MemLp (halaszTorusWindow δ) 2 (halaszVinogradovHaar k) :=
  (memLp_const (1:ℂ)).indicator (halasz_torus_window_measurable_set δ)

lemma halasz_torus_window_norm_square {k : ℕ} (δ : Fin k → ℝ)
    (α : Fin k → AddCircle (1:ℝ)) :
    ‖halaszTorusWindow δ α‖^2=
      ∏ j,(closedBall (0:AddCircle (1:ℝ)) (δ j)).indicator (fun _ => (1:ℝ)) (α j) := by
  rw [halasz_torus_window_product,norm_prod,← Finset.prod_pow]
  apply prod_congr rfl
  intro j _
  by_cases h : α j∈closedBall (0:AddCircle (1:ℝ)) (δ j) <;>
    simp [halaszCircleWindow,h]

lemma halasz_torus_window_square_integral {k : ℕ} (δ : Fin k → ℝ)
    (hδ : ∀ j, 0≤δ j) (hδhalf : ∀ j,δ j≤1/2) :
    (∫ α, ‖halaszTorusWindow δ α‖^2 ∂halaszVinogradovHaar k)=∏ j,2*δ j := by
  simp_rw [halasz_torus_window_norm_square]
  unfold halaszVinogradovHaar
  rw [integral_fintype_prod_eq_prod]
  apply prod_congr rfl
  intro j _
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul,mul_one,
    halasz_circle_window_volume (hδ j) (hδhalf j)]

lemma halasz_torus_window_coefficient {k : ℕ} (δ : Fin k → ℝ) (m : Fin k → ℤ)
    (hδ : ∀ j,0≤δ j) (hδhalf : ∀ j,δ j≤1/2)
    (hphase : ∀ j,2*Real.pi*|(m j:ℝ)| * δ j≤1) :
    (∏ j,δ j)≤‖∫ α,conj (halaszVinogradovCharacter m α)*halaszTorusWindow δ α
      ∂halaszVinogradovHaar k‖ := by
  simp_rw [halasz_torus_window_product,halaszVinogradovCharacter,map_prod,← prod_mul_distrib]
  unfold halaszVinogradovHaar
  change (∏ j,δ j)≤‖∫ α,∏ j,(fun x : AddCircle (1:ℝ) =>
    conj (fourier (m j) x)*halaszCircleWindow (δ j) x) (α j)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)‖
  have hi := integral_fintype_prod_eq_prod
    (E := fun _ : Fin k => AddCircle (1:ℝ))
    (μ := fun _ : Fin k => AddCircle.haarAddCircle)
    (fun j x => conj (fourier (m j) x)*halaszCircleWindow (δ j) x)
  rw [hi,norm_prod]
  apply prod_le_prod₀ (fun j _ => hδ j)
  intro j _
  exact halasz_circle_window_coefficient (hδ j) (hδhalf j) (hphase j)

end TwoPointCorrelations

end OAI
