import OAI.Probability.DilutedSpin.PoissonCountThinning
import OAI.Probability.DilutedSpin.UpperReplicaPatterns

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma rawReplicaMoment_eq_product {p n : ℕ} (M : Model p)
    (P : Fin p → FiniteLaw (Fin n → Spin)) :
    rawReplicaMoment M P=∫ z : InteractionSample p,(-z.2.2.1)^n*
      ∏ l : Fin p,(P l).expect (fun s => ∏ a : Fin n,z.2.2.2 l (s a)) ∂M.disorder.toMeasure := by
  unfold rawReplicaMoment
  apply integral_congr_ae
  filter_upwards [] with z
  have he (s : Fin p → Fin n → Spin) :
      (∏ a : Fin n,(-z.2.2.1)*∏ l : Fin p,z.2.2.2 l (s l a))=
        (-z.2.2.1)^n*∏ l : Fin p,∏ a : Fin n,z.2.2.2 l (s l a) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [Finset.prod_comm]
  simp_rw [he]
  rw [FiniteLaw.expect_mul_left]
  congr 1
  exact FiniteLaw.expect_pi_product P (fun l s => ∏ a : Fin n,z.2.2.2 l (s a))

lemma freshPatternFeature_raw {Z : Type} [Fintype Z] {n : ℕ}
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (f : Spin → ℝ) :
    (freshPatternLaw Q x).expect (fun s => ∏ a : Fin n,f (s a))=
      Q.expect (fun z => ∏ a : Fin n,averagedFactor f (x z a)) := by
  unfold freshPatternLaw
  rw [FiniteLaw.expect_map,FiniteLaw.expect_bind]
  apply FiniteLaw.expect_congr
  intro z
  exact FiniteLaw.expect_pi_product _ _

lemma raw_mixedPatternMoment {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    rawReplicaMoment M (fun l : Fin p => if sel l then oldPatternLaw old else freshPatternLaw Q x) =
      ∫ z : InteractionSample p,(-z.2.2.1)^n *
        (∏ l : Fin p, if sel l then
          (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun i => ∏ a : Fin n,z.2.2.2 l (old i a))
        else Q.expect (fun w => ∏ a : Fin n,averagedFactor (z.2.2.2 l) (x w a)))
      ∂M.disorder.toMeasure := by
  rw [rawReplicaMoment_eq_product]
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  cases sel l
  · simp only [Bool.false_eq_true,↓reduceIte]
    exact freshPatternFeature_raw Q x _
  · simp only [↓reduceIte]
    exact FiniteLaw.expect_map _ _ _

/-- Averaging an inserted factor against arbitrary independent spin laws
preserves the original uniform interaction bound. -/
lemma averaged_product_bound {p : ℕ} (b : ℝ) (f : Fin p → Spin → ℝ)
    (h : ∀ s : Fin p → Spin,|b*∏ l,f l (s l)|≤1)
    (P : Fin p → FiniteLaw Spin) : |b*∏ l,(P l).expect (f l)|≤1 := by
  rw [← FiniteLaw.expect_pi_product,← FiniteLaw.expect_mul_left]
  exact FiniteLaw.abs_expect_le _ h

end DilutedSpinGlass

end

end OAI
