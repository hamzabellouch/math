import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedOuterCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductModel

namespace OAI

/-! The true squarefree product model with a fixed-angular outer coefficient. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_stopped_product_model_norm (ℓ : ℤ) (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P B : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
      (β : Eisenstein → ℂ) (X Y M u : ℝ),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ Y → 0 < X → 0 ≤ M →
      (∀ a ∈ P, primary a) → (∀ b ∈ B, primary b) →
      (∀ a ∈ P, ∀ b ∈ B, X ≤ norm (a*b) ∧ norm (a*b) ≤ Y) →
      (∀ b ∈ B, ‖β b‖ ≤ M) →
      ‖squarefreeProductModel P B (angularStoppedAlpha ℓ E U ψ w remaining) β u‖ ≤
        K*M*Y*X^(-1/6:ℝ)*(1+Real.log Y)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_fixed_divisor_moment hpnt 4 (by norm_num)
  refine ⟨K,d,hK,?_⟩
  intro E U P B ψ w remaining β X Y M u hE hψ hY hX hM hP hB hnorm hβ
  let S := squarefreePairSupport P B
  let γ := primaryPairCoefficient P B (fun p => angularStoppedAlpha ℓ E U ψ w remaining p.1*β p.2)
  have hS (n : Eisenstein) (hn : n ∈ S) :
      primary n ∧ Squarefree n ∧ X ≤ norm n ∧ norm n ≤ Y := by
    have hs := squarefreePairSupport_primary P B hP hB hn
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hn).1
    have hm := Finset.mem_product.mp hp
    exact ⟨hs.1,hs.2,he ▸ (hnorm p.1 hm.1 p.2 hm.2)⟩
  have hγ : ∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card := by
    intro n hn
    apply (squarefree_pair_coefficient_bound P B _ β zero_le_one hM hP
      (fun a ha hsf => ?_) hβ (hS n hn).1 (hS n hn).2.1).trans_eq (by rw [one_mul])
    rw [angularStoppedAlpha_norm ℓ E U ψ w remaining (hP a ha)]
    simpa only [one_mul] using (stoppedAlpha_divisor_bound E U hE hψ w remaining a).trans
      (show ((E.filter (fun e => e ∣ a)).card:ℝ) ≤
        (2:ℝ)^(primaryPrimeFactors a).card by
          exact_mod_cast primary_squarefree_divisor_card E hE (hP a ha) hsf)
  rw [squarefreeProductModel_collection]
  apply (divisor_model_norm_bound S γ hX hM (fun n hn => (hS n hn).2.2.1) hγ u).trans
  calc
    _ ≤ M*X^(-1/6:ℝ)*(K*Y*(1+Real.log Y)^d) :=
      mul_le_mul_of_nonneg_left (hmoment Y S hY
        (fun n hn => ⟨(hS n hn).1,(hS n hn).2.1,(hS n hn).2.2.2⟩)) (by positivity)
    _ = _ := by ring


end CubicFirstMoment

end

end OAI
