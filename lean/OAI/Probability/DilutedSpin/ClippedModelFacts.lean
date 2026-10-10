import OAI.Probability.DilutedSpin.CompoundRate
import OAI.Probability.DilutedSpin.FunctionalStability
import OAI.Probability.DilutedSpin.UpperMoments

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal

lemma clippedModel_interaction_bounded {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᵐ z ∂(clippedModel M K).disorder.toMeasure, ‖z.1‖ ≤ K := by
  change ∀ᵐ z ∂Measure.map (clipSample K) M.disorder.toMeasure, ‖z.1‖ ≤ K
  apply (ae_map_iff (measurable_clipSample K).aemeasurable (measurableSet_le measurable_fst.norm measurable_const)).mpr
  exact ae_of_all _ (fun z => (pi_norm_le_iff_of_nonneg hK).mpr (fun s => by
    simpa only [Real.norm_eq_abs,clipSample] using clipReal_bound hK (z.1 s)))

lemma clippedModel_field_bounded {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    ∀ᵐ h ∂(clippedModel M K).field.toMeasure, |h| ≤ K := by
  change ∀ᵐ h ∂Measure.map (clipReal K) M.field.toMeasure, |h| ≤ K
  apply (ae_map_iff (measurable_clipReal K).aemeasurable (measurableSet_le measurable_id.abs measurable_const)).mpr
  exact ae_of_all _ (clipReal_bound hK)

lemma clippedModel_interaction_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    Integrable (fun z : InteractionSample p => ‖z.1‖) (clippedModel M K).disorder.toMeasure := by
  exact (integrable_const K).mono' (by fun_prop) ((clippedModel_interaction_bounded M hK).mono (fun z hz => by simpa only [norm_norm] using hz))

lemma clippedModel_field_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K) :
    Integrable (fun h : ℝ => |h|) (clippedModel M K).field.toMeasure := by
  exact (integrable_const K).mono' (by fun_prop) ((clippedModel_field_bounded M hK).mono (fun z hz => by simpa only [Real.norm_eq_abs,abs_abs] using hz))

lemma clippedModel_symmetric {p : ℕ} (M : Model p) (K : ℝ)
    (hsym : ∀ e : Equiv.Perm (Fin p),IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i))) M.disorder.toMeasure M.disorder.toMeasure)
    (e : Equiv.Perm (Fin p)) :
    IdentDistrib (fun z : InteractionSample p => z.1)
      (fun z : InteractionSample p => fun s => z.1 (fun i => s (e i)))
      (clippedModel M K).disorder.toMeasure (clippedModel M K).disorder.toMeasure := by
  constructor
  · exact measurable_fst.aemeasurable
  · exact (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop).aemeasurable
  · change Measure.map _ (Measure.map (clipSample K) M.disorder.toMeasure)=Measure.map _ (Measure.map (clipSample K) M.disorder.toMeasure)
    rw [Measure.map_map measurable_fst (measurable_clipSample K),
      Measure.map_map (show Measurable (fun z : InteractionSample p => fun (s : Fin p → Spin) => z.1 (fun l => s (e l))) by fun_prop) (measurable_clipSample K)]
    exact (interaction_clip_symmetric M K hsym e).map_eq

lemma clip_interaction_difference_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K)
    (hi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure) :
    Integrable (fun z => ‖(clipSample K z).1-z.1‖) M.disorder.toMeasure := by
  apply (hi.const_mul 2).mono' ((measurable_fst.comp (measurable_clipSample K)).sub measurable_fst).norm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simp only [norm_norm]
    change ‖(clipSample K z).1-z.1‖ ≤ 2*‖z.1‖
    rw [norm_sub_rev]
    exact clipSample_difference_bound hK z)

lemma clip_field_difference_integrable {p : ℕ} (M : Model p) {K : ℝ} (hK : 0 ≤ K)
    (hi : Integrable (fun h : ℝ => |h|) M.field.toMeasure) :
    Integrable (fun h => |clipReal K h-h|) M.field.toMeasure := by
  apply (hi.const_mul 2).mono' ((measurable_clipReal K).sub measurable_id).abs.aestronglyMeasurable
  exact ae_of_all _ (fun h => by
    simp only [Real.norm_eq_abs,abs_abs]
    change |clipReal K h-h| ≤ 2*|h|
    have h1 := abs_sub (clipReal K h) h
    have h2 := clipReal_abs_le hK h
    linarith)
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def replicaInsertionMoment {p n : ℕ} (M : Model p) (R : ℝ)
    (P : Fin p → FiniteLaw (Fin n → Spin)) : ℝ :=
  ∫ z : InteractionSample p, (-z.2.2.1)^n*(FiniteLaw.pi P).expect
    (fun s => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) ∂M.disorder.toMeasure

/-- The literal order-n replica coefficient of the three independent-label
insertions. The old spin-pattern law P and fresh-label spin-pattern law B
are arbitrary; their laws are not assumed to agree. -/
lemma replicaInsertion_combination {p n : ℕ} (M : Model p) (hM : Admissible M)
    (j : Fin p) (R : ℝ) (P B : FiniteLaw (Fin n → Spin)) :
    replicaInsertionMoment M R (fun _ : Fin p => P) -
      (p:ℝ)*replicaInsertionMoment M R (fun l : Fin p => if l=j then P else B) +
      ((p-1:ℕ):ℝ)*replicaInsertionMoment M R (fun _ : Fin p => B) =
    (∫ z : InteractionSample p,(-z.2.2.1)^n ∂M.disorder.toMeasure)*
      ((∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)^p -
       (p:ℝ)*(∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)*
         (∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure)^(p-1) +
       ((p-1:ℕ):ℝ)*(∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure)^p) := by
  classical
  unfold replicaInsertionMoment
  rw [upper_pattern_moment M hM j,upper_pattern_moment M hM j,upper_pattern_moment M hM j]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have he : (∏ l : Fin p, ∫ z : InteractionSample p,
      patternFeature R (if l=j then P else B) (z.2.2.2 j) ∂M.disorder.toMeasure) =
    (∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)*
     (∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure)^(p-1) := by
    convert product_one_distinguished j
      (∫ z : InteractionSample p,patternFeature R P (z.2.2.2 j) ∂M.disorder.toMeasure)
      (∫ z : InteractionSample p,patternFeature R B (z.2.2.2 j) ∂M.disorder.toMeasure) using 1
    · apply Finset.prod_congr rfl
      intro l _
      split_ifs <;> rfl
    · simp
  rw [he]
  ring

lemma replicaInsertion_coefficient_nonpos {p n : ℕ} (M : Model p) (hM : Admissible M)
    (hn : 1≤n) (j : Fin p) (R t : ℝ) (ht : 0≤t) (P B : FiniteLaw (Fin n → Spin)) :
    -(t^n/(n:ℝ))*(replicaInsertionMoment M R (fun _ : Fin p => P) -
      (p:ℝ)*replicaInsertionMoment M R (fun l : Fin p => if l=j then P else B) +
      ((p-1:ℕ):ℝ)*replicaInsertionMoment M R (fun _ : Fin p => B)) ≤ 0 := by
  rw [replicaInsertion_combination M hM j, ← mul_assoc]
  exact admissible_upper_coefficient_nonpos M hM n hn t _ _ ht

end DilutedSpinGlass

end

end OAI
