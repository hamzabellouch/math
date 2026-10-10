import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble
import OAI.Analysis.CoulombRadii.RandomFields.EnsembleCauchy
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawRMS

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma potentialForm_bounded_add {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x|≤B) (hC : ∀ x, |g x|≤C) :
    potentialForm (fun x => f x+g x) ψ=potentialForm f ψ+potentialForm g ψ := by
  simp only [potentialForm,add_mul,integral_add (boundedObservable_integrable ψ f hf hB _)
    (boundedObservable_integrable ψ g hg hC _),Finset.sum_add_distrib]

lemma coreConditionalObservable_nonneg {m k : ℕ} (ψ : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : ∀ x, 0≤W x) (s : Spins m) (x : Configuration m) :
    0≤coreConditionalObservable ψ W s x := potentialForm_nonneg _ _ (fun _ => hW _)

lemma coreConditionalObservable_mono {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Configuration (m+k) → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x|≤B) (hC : ∀ x, |g x|≤C) (hfg : ∀ x, f x≤g x)
    (s : Spins m) (x : Configuration m) :
    coreConditionalObservable ψ f s x≤coreConditionalObservable ψ g s x := by
  exact potentialForm_mono_bounded _ _ _
    (hf.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (hg.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (fun _ => hB _) (fun _ => hC _) (fun _ => hfg _)

lemma coreConditionalObservable_add {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Configuration (m+k) → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x|≤B) (hC : ∀ x, |g x|≤C)
    (s : Spins m) (x : Configuration m) :
    coreConditionalObservable ψ (fun z => f z+g z) s x=
      coreConditionalObservable ψ f s x+coreConditionalObservable ψ g s x := by
  exact potentialForm_bounded_add _ _ _
    (hf.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (hg.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (fun _ => hB _) (fun _ => hC _)

lemma coreConditionalObservable_square_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ x, |W x|≤B) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*(coreConditionalObservable ψ W s x)^2) := by
  apply (mass_coreSlice_integrable ψ s).mul_bdd
    ((coreConditionalObservable_aestronglyMeasurable ψ W hW hB s).pow 2)
  filter_upwards [] with x
  change ‖(coreConditionalObservable ψ W s x)^2‖ ≤ B^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (coreConditionalObservable_abs_le ψ W hW hB0 hB s x) 2

lemma potentialForm_normalized_square_le {n : ℕ} (ψ : H1Vector n)
    (W : Configuration n → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x|≤B) :
    (potentialForm W ψ.normalized)^2 ≤ potentialForm (fun x => (W x)^2) ψ.normalized := by
  have H := potentialForm_bounded_cauchy ψ.normalized W (fun _ => 1) hW measurable_const hB (fun _ => le_rfl)
  simp only [mul_one,one_pow,potentialForm_const,one_mul] at H
  exact H.trans (by nlinarith [mass_normalized_le_one ψ,
    potentialForm_nonneg ψ.normalized (fun x => (W x)^2) (fun _ => sq_nonneg _)])

lemma slice_conditional_square_le {m k : ℕ} (ψ : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ x, |W x|≤B) :
    sliceExpectation ψ (fun s x => (coreConditionalObservable ψ W s x)^2) ≤
      potentialForm (fun x => (W x)^2) ψ := by
  have hB2 (x) : |(W x)^2|≤B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  rw [←sliceExpectation_coreConditionalObservable ψ _ (hW.pow_const 2) hB2]
  apply sliceExpectation_mono_ae ψ _ _
    (coreConditionalObservable_square_weight_integrable ψ W hW hB0 hB)
    (coreConditionalObservable_weight_integrable ψ _ (hW.pow_const 2) (sq_nonneg _) hB2)
  intro s
  filter_upwards [] with x
  exact potentialForm_normalized_square_le _ _
    (hW.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (fun _ => hB _)

namespace RecordedEnsemble
variable {n : ℕ}
def dataRMS (T : RecordedEnsemble n)
    (F : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ) : ℝ :=
  Real.sqrt (∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))
lemma dataRMS_nonneg (T : RecordedEnsemble n) (F) : 0≤T.dataRMS F := Real.sqrt_nonneg _
lemma dataRMS_sq (T : RecordedEnsemble n) (F) :
    T.dataRMS F^2=∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2) :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _)))))

lemma dataRMS_mono (T : RecordedEnsemble n) (F G)
    (hF : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2))
    (hG : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(G p s x)^2))
    (hF0 : ∀ p s x, 0≤F p s x) (hFG : ∀ p s x, F p s x≤G p s x) : T.dataRMS F≤T.dataRMS G := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro p hp
  exact sliceExpectation_mono_ae _ _ _ (hF p) (hG p) (fun s => Eventually.of_forall (fun x =>
    pow_le_pow_left₀ (hF0 p s x) (hFG p s x) 2))

lemma dataRMS_add (T : RecordedEnsemble n) (F G)
    (hF : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2))
    (hG : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(G p s x)^2))
    (hFG : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x*G p s x))) :
    T.dataRMS (fun p s x => F p s x+G p s x) ≤ T.dataRMS F+T.dataRMS G := by
  have he : T.dataRMS (fun p s x => F p s x+G p s x)^2 =
      T.dataRMS F^2+2*(∑ p, sliceExpectation (T.vector p) (fun s x => F p s x*G p s x))+T.dataRMS G^2 := by
    simp only [dataRMS_sq,sliceExpectation]
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hi : Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2+
        2*(mass ((T.vector p).coreSlice s x)*(F p s x*G p s x))) := (hF p s).add ((hFG p s).const_mul 2)
    calc
      _ = ∫ x, (mass ((T.vector p).coreSlice s x)*(F p s x)^2+
          2*(mass ((T.vector p).coreSlice s x)*(F p s x*G p s x)))+
          mass ((T.vector p).coreSlice s x)*(G p s x)^2 := integral_congr_ae (Eventually.of_forall (fun _ => by ring))
      _ = _ := by rw [integral_add hi (hG p s),integral_add (hF p s) ((hFG p s).const_mul _),integral_const_mul]
  have hcs := slice_ensemble_cauchy T.out T.core T.vector F G hF hG hFG
  rw [←dataRMS_sq,←dataRMS_sq] at hcs
  have H : (∑ p, sliceExpectation (T.vector p) (fun s x => F p s x*G p s x)) ≤T.dataRMS F*T.dataRMS G := by
    exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (mul_nonneg (T.dataRMS_nonneg F) (T.dataRMS_nonneg G))).mp
      (by simpa only [sq_abs,mul_pow] using hcs))
  nlinarith [T.dataRMS_nonneg F,T.dataRMS_nonneg G,T.dataRMS_nonneg (fun p s x => F p s x+G p s x)]

theorem Conserves.dataRMS_conditional_le {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) (W : Configuration n → ℝ) (hW : Measurable W)
    {B : ℝ} (hB0 : 0≤B) (hB : ∀ x, |W x|≤B) :
    T.dataRMS (fun p => coreConditionalObservable (T.vector p) (W ∘ reindexConfiguration (T.labels p))) ≤rawRMS ψ W := by
  apply Real.sqrt_le_sqrt
  have hB2 (x) : |(W x)^2|≤B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => slice_conditional_square_le (T.vector p)
    (W ∘ reindexConfiguration (T.labels p)) (hW.comp (reindexConfiguration_continuous _).measurable)
    hB0 (fun x => hB _))
  exact H.trans_eq (hT (fun x => (W x)^2) (hW.pow_const 2) ⟨B^2,hB2⟩)

end RecordedEnsemble
end Coulomb
end

end

end OAI
