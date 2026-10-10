import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.FourierPolynomialSmoothing

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

lemma chain_split (P : ℕ → Prop) {g p : ℕ} (hgp : g ≤ p) (hg : P g) :
    P p ∨ ∃ h ∈ Finset.Ico g p, P h ∧ ¬P (h+1) := by
  classical
  induction p, hgp using Nat.le_induction with
  | base => exact Or.inl hg
  | succ p hgp ih =>
    rcases ih with hp | ⟨h,hh,hhx⟩
    · by_cases hn : P (p+1)
      · exact Or.inl hn
      · exact Or.inr ⟨p,Finset.mem_Ico.mpr ⟨hgp,by omega⟩,hp,hn⟩
    · exact Or.inr ⟨h,Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hh).1,by have := (Finset.mem_Ico.mp hh).2; omega⟩,hhx⟩

lemma chain_filter_card {α : Type*} [DecidableEq α] (T : ℕ → Finset α)
    (P : α → Prop) [DecidablePred P] {g p : ℕ} (hgp : g ≤ p) :
    ((T g).filter P).card ≤ (T p).card+
      ∑ h ∈ Finset.Ico g p, (((T h)\(T (h+1))).filter P).card := by
  classical
  have hsub : (T g).filter P ⊆ T p ∪ (Finset.Ico g p).biUnion
      (fun h => (((T h)\(T (h+1))).filter P)) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx,hP⟩
    rcases chain_split (fun h => x ∈ T h) hgp hx with hp | ⟨h,hh,h₁,h₂⟩
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨h,hh,Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨h₁,h₂⟩,hP⟩⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_biUnion_le) _))

variable {V α : Type*} [MeasurableSpace V]

lemma measurable_finite_test_count (T : Finset α) (F : α → Set V)
    (hF : ∀ a ∈ T, MeasurableSet (F a)) :
    Measurable (fun w => (((T.filter fun a => w ∈ F a).card:ℕ):ℝ)) := by
  classical
  have he : (fun w => (((T.filter fun a => w ∈ F a).card:ℕ):ℝ)) =
      fun w => ∑ a ∈ T, (F a).indicator (fun _ => (1:ℝ)) w := by
    funext w
    rw [Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : w ∈ F a <;> simp [h]
  rw [he]
  exact Finset.measurable_sum _ (fun a ha => measurable_const.indicator (hF a ha))

lemma integral_finite_test_count (ξ : Measure V) [IsFiniteMeasure ξ]
    (T : Finset α) (F : α → Set V) (hF : ∀ a ∈ T, MeasurableSet (F a)) :
    (∫ w, (((T.filter fun a => w ∈ F a).card:ℕ):ℝ) ∂ξ) = ∑ a ∈ T, ξ.real (F a) := by
  classical
  have he : (fun w => (((T.filter fun a => w ∈ F a).card:ℕ):ℝ)) =
      fun w => ∑ a ∈ T, (F a).indicator (fun _ => (1:ℝ)) w := by
    funext w
    rw [Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : w ∈ F a <;> simp [h]
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    simp [integral_indicator (hF a ha),measureReal_def]
  · intro a ha
    exact (integrable_const _).indicator (hF a ha)

lemma integrable_finite_test_count (ξ : Measure V) [IsFiniteMeasure ξ]
    (T : Finset α) (F : α → Set V) (hF : ∀ a ∈ T, MeasurableSet (F a)) :
    Integrable (fun w => (((T.filter fun a => w ∈ F a).card:ℕ):ℝ)) ξ := by
  apply (integrable_const (T.card:ℝ)).mono' (measurable_finite_test_count T F hF).aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Finset.card_filter_le T (fun a => w ∈ F a)

lemma integral_chain_filter_le (ξ : Measure V) [IsFiniteMeasure ξ] [DecidableEq α]
    (T : ℕ → Finset α) (F : α → Set V) (hF : ∀ a, MeasurableSet (F a))
    {g p : ℕ} (hgp : g ≤ p) (hmass : ξ univ ≤ 1) :
    (∫ w, (((T g).filter fun a => w ∈ F a).card:ℝ) ∂ξ) ≤
      ((T p).card:ℝ)+∑ h ∈ Finset.Ico g p, ∑ a ∈ T h \ T (h+1), ξ.real (F a) := by
  classical
  have hi : Integrable (fun w => ((T p).card:ℝ)+∑ h ∈ Finset.Ico g p,
      (((T h\T (h+1)).filter fun a => w ∈ F a).card:ℝ)) ξ :=
    (integrable_const _).add (integrable_finsetSum _ (fun h _ => integrable_finite_test_count ξ _ F (fun a _ => hF a)))
  have hm := integral_mono (integrable_finite_test_count ξ (T g) F (fun a _ => hF a)) hi
    (fun w => by
      have hc := (Nat.cast_le (α:=ℝ)).mpr (chain_filter_card T (fun a => w ∈ F a) hgp)
      simpa only [Nat.cast_add,Nat.cast_sum] using hc)
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun h _ =>
    integrable_finite_test_count ξ _ F (fun a _ => hF a))),integral_finsetSum] at hm
  · simp_rw [integral_finite_test_count ξ _ F (fun a _ => hF a)] at hm
    rw [integral_finite_test_count ξ (T g) F (fun a _ => hF a)]
    apply hm.trans
    apply add_le_add _ le_rfl
    rw [integral_const,smul_eq_mul]
    have hh : (ξ univ).toReal ≤ 1 := ENNReal.toReal_mono (by simp) hmass |>.trans_eq (by simp)
    simpa only [measureReal_def,one_mul] using mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) (T p).card)
  · intro h hh
    exact integrable_finite_test_count ξ _ F (fun a _ => hF a)
end GraphLiteralSupport.CurrentFalconer.Exceptional
end
end

end OAI
