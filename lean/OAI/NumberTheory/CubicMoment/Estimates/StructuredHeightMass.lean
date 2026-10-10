import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicStructuredMeanValue
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeOrdinaryBounds

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuous_fullStructuredAngularSum (R : ℝ) (h v e : Eisenstein) (ℓ : ℤ) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    Continuous (fun t : ℝ => fullStructuredAngularSum R h v e ℓ (t+u) W X) := by
  simp_rw [fullStructuredAngularSum_eq]
  apply continuous_finsetSum
  intro z _
  apply continuous_const.mul
  unfold mellinPhase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      ((continuous_id.add continuous_const).mul continuous_const)).mul continuous_const)

lemma finite_dyadic_integral_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ a ∈ S, f a t) + (∫ t in -2*T..-T, ∑ a ∈ S, f a t))/T =
      ∑ a ∈ S, ((∫ t in T..2*T, f a t)+(∫ t in -2*T..-T, f a t))/T := by
  rw [intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    ← Finset.sum_add_distrib,Finset.sum_div]

lemma residual_support_card_le (Ram J H S T : Finset Eisenstein)
    (hH : H ⊆ coprimeResidualSupport Ram J (coprimePairs S T)) :
    H.card ≤ Ram.card*J.card*(S.card*T.card) := by
  have hP : (coprimePairs S T).card ≤ S.card*T.card := by
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product S T)
  calc
    _ ≤ (coprimeResidualSupport Ram J (coprimePairs S T)).card := Finset.card_le_card hH
    _ ≤ ((Ram.product J).product (coprimePairs S T)).card := Finset.card_image_le
    _ = Ram.card*J.card*(coprimePairs S T).card :=
      (Finset.card_product (Ram.product J) (coprimePairs S T)).trans
        (congrArg (fun n => n*(coprimePairs S T).card) (Finset.card_product Ram J))
    _ ≤ _ := Nat.mul_le_mul_left _ hP

lemma residual_dyadic_row_count {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (Ram J H S T : Finset Eisenstein)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ 2*P)
    (hT : ∀ t ∈ T, primary t ∧ norm t ≤ 2*Q)
    (hH : H ⊆ coprimeResidualSupport Ram J (coprimePairs S T)) :
    (H.card:ℝ) ≤ 1296*(Ram.card:ℝ)*J.card*(P*Q) := by
  have hs : (S.card:ℝ) ≤ 36*P := by
    have hh := primary_support_card_le S (by positivity : 0 ≤ 2*P) hS
    linarith
  have ht : (T.card:ℝ) ≤ 36*Q := by
    have hh := primary_support_card_le T (by positivity : 0 ≤ 2*Q) hT
    linarith
  have hc : (H.card:ℝ) ≤ (Ram.card:ℝ)*J.card*((S.card:ℝ)*T.card) := by
    exact_mod_cast residual_support_card_le Ram J H S T hH
  calc
    _ ≤ (Ram.card:ℝ)*J.card*((36*P)*(36*Q)) :=
      hc.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hs ht (Nat.cast_nonneg _) (by positivity))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    _ = _ := by ring

def fullStructuredHeightMass (R : ℝ) (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ h ∈ H, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2

lemma fullStructuredHeightMass_le {R D T : ℝ} (H : Finset Eisenstein) (v e : Eisenstein)
    (ℓ : ℤ) (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hrow : ∀ h ∈ H,
      ((∫ t in T..2*T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2) +
       (∫ t in -2*T..-T, ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2))/T ≤ D) :
    ((∫ t in T..2*T, fullStructuredHeightMass R H v e ℓ u W X t)+
     (∫ t in -2*T..-T, fullStructuredHeightMass R H v e ℓ u W X t))/T ≤ H.card*D := by
  unfold fullStructuredHeightMass
  rw [finite_dyadic_integral_sum H
    (fun h t => ‖fullStructuredAngularSum R h v e ℓ (t+u) W X‖^2) (fun h _ =>
    ((continuous_fullStructuredAngularSum R h v e ℓ u W X).norm).pow 2) T]
  calc
    _ ≤ ∑ _h ∈ H, D := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end CubicFirstMoment

end

end OAI
