import Mathlib
import OAI.Probability.Ballisticity.Estimates.IidListProcess

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma integral_partialSumMax_square_le_sum_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  let w : ℝ≥0 := ⟨z,hz⟩
  let Y := fun k ω => symmetricClip w (X k ω)
  have hY (k) : Measurable (Y k) := (symmetricClip w).continuous.measurable.comp (hX k)
  have he (k) : Y k =ᵐ[μ] X k := by
    filter_upwards [hbound k] with ω hω
    exact symmetricClip_eq_self w hω
  have hYe := ae_all_iff.mpr he
  have hInd : iIndepFun Y μ := hind.comp (fun _ => symmetricClip w) (fun _ => (symmetricClip w).continuous.measurable)
  have hm (k) : ∫ ω, Y k ω ∂μ = 0 := (integral_congr_ae (he k)).trans (hmean k)
  have hc := integral_partialSumMax_square_le_sum μ Y hY hInd hm hz
    (fun k ω => symmetricClip_bound w _) n
  have hleft : (∫ ω, (partialSumMax (fun k => Y k ω) n)^2 ∂μ) =
      ∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hYe] with ω hω
    rw [funext hω]
  have hright (k) : (∫ ω, (Y k ω)^2 ∂μ) = ∫ ω, (X k ω)^2 ∂μ :=
    integral_congr_ae ((he k).fun_comp fun x => x^2)
  simpa only [hleft,hright] using hc

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma integrable_abs_sub_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (b B : ℝ) (hb : ∀ᵐ ω ∂μ, |F ω-b| ≤ B) : Integrable F μ := by
  apply Integrable.of_bound hF.aestronglyMeasurable (B+|b|)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs]
  calc |F ω| = |(F ω-b)+b| := by congr 1; ring
       _ ≤ |F ω-b|+|b| := abs_add_le _ _
       _ ≤ B+|b| := add_le_add hω le_rfl

lemma abs_mean_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F)
    (b B : ℝ) (hb : ∀ᵐ ω ∂μ, |F ω-b| ≤ B) : |(∫ ω, F ω ∂μ)-b| ≤ B := by
  have hi := integrable_abs_sub_bounded μ F hF b B hb
  have he : (∫ ω, F ω-b ∂μ) = (∫ ω, F ω ∂μ)-b := by
    rw [integral_sub hi (integrable_const b),integral_const,probReal_univ,one_smul]
  rw [← he,← Real.norm_eq_abs]
  have hn := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => F ω-b)
    (C := B) (by simpa only [Real.norm_eq_abs] using hb)
  simpa only [probReal_univ,mul_one] using hn

lemma integral_centered_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : Measurable F) (b : ℝ) :
    (∫ ω, (F ω-(∫ x, F x ∂μ))^2 ∂μ) ≤ ∫ ω, (F ω-b)^2 ∂μ := by
  rw [← variance_eq_integral hF.aemeasurable,← variance_sub_const hF.aestronglyMeasurable b]
  exact variance_le_expectation_sq (hF.sub_const b).aestronglyMeasurable

lemma iidList_integral_max_square_le {G : Type*} [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (p : PMF G) (F : G → ℝ) (b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ u ∂p.toMeasure, |F u-b| ≤ B) (n : ℕ) :
    (∫ w, (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2 ∂(iidListPMF p n).toMeasure) ≤
      4*(n:ℝ)*(∫ u, (F u-b)^2 ∂p.toMeasure) := by
  obtain ⟨Ω,mΩ,μ,X,hX,hLaw,hind,hprob⟩ := exists_iid ℕ p.toMeasure
  let := mΩ
  let := hprob
  let c := ∫ u, F u ∂p.toMeasure
  let Y := fun k ω => F (X k ω)-c
  have hF : Measurable F := measurable_of_countable F
  have hFB := integrable_abs_sub_bounded p.toMeasure F hF b B hbound
  have hcb : |c-b| ≤ B := abs_mean_sub_le p.toMeasure F hF b B hbound
  have hY (k) : Measurable (Y k) := (hF.comp (hX k)).sub_const c
  have hYB (k) : ∀ᵐ ω ∂μ, |Y k ω| ≤ 2*B := by
    have hb : ∀ᵐ ω ∂μ, |F (X k ω)-b| ≤ B :=
      (hLaw k).ae_iff (by fun_prop) |>.mpr hbound
    filter_upwards [hb] with ω hω
    calc |Y k ω| = |(F (X k ω)-b)-(c-b)| := by congr 1; dsimp [Y]; ring
         _ ≤ |F (X k ω)-b|+|c-b| := abs_sub _ _
         _ ≤ 2*B := by linarith
  have hYi (k) : Integrable (fun ω => F (X k ω)) μ := by
    have hi : Integrable F (μ.map (X k)) := by rw [(hLaw k).map_eq]; exact hFB
    exact hi.comp_measurable (hX k)
  have hmean (k) : ∫ ω, Y k ω ∂μ = 0 := by
    change (∫ ω, F (X k ω)-c ∂μ) = 0
    rw [integral_sub (hYi k) (integrable_const c),integral_const,probReal_univ,one_smul]
    have he := (hLaw k).integral_comp hF.aestronglyMeasurable
    simp only [Function.comp_apply] at he
    rw [he]; exact sub_self _
  have hInd : iIndepFun Y μ := hind.comp (fun _ u => F u-c) (fun _ => hF.sub_const c)
  have hm := integral_partialSumMax_square_le_sum_ae μ Y hY hInd hmean (by positivity) hYB n
  have hs (k) : (∫ ω, (Y k ω)^2 ∂μ) ≤ ∫ u, (F u-b)^2 ∂p.toMeasure := by
    change (∫ ω, (F (X k ω)-c)^2 ∂μ) ≤ _
    have he := (hLaw k).integral_comp (by fun_prop : AEStronglyMeasurable (fun u => (F u-c)^2) p.toMeasure)
    simp only [Function.comp_apply] at he
    rw [he]
    exact integral_centered_square_le p.toMeasure F hF b
  have hl := iid_list_hasLaw μ p X hX hLaw hind n
  have he := hl.integral_comp (by fun_prop : AEStronglyMeasurable
    (fun w => (listCenteredMax F c w)^2) (iidListPMF p n).toMeasure)
  simp only [Function.comp_apply] at he
  have he2 : (∫ ω, (partialSumMax (fun k => Y k ω) n)^2 ∂μ) =
      ∫ w, (listCenteredMax F c w)^2 ∂(iidListPMF p n).toMeasure := by
    rw [← he]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => congrArg (fun x : ℝ => x^2)
      (listCenteredMax_ofFn F c (fun k => X k ω) n).symm)
  rw [← he2]
  calc _ ≤ 4*∑ k ∈ Finset.range n, ∫ ω, (Y k ω)^2 ∂μ := hm
       _ ≤ 4*∑ _k ∈ Finset.range n, ∫ u, (F u-b)^2 ∂p.toMeasure :=
         mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hs k)) (by norm_num)
       _ = 4*(n:ℝ)*(∫ u, (F u-b)^2 ∂p.toMeasure) := by
         simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma integrable_partialSumMax_pow_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k, ∀ᵐ ω ∂μ, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^p) μ := by
  apply Integrable.of_bound ((measurable_partialSumMax X hX n).pow_const p).aestronglyMeasurable ((n*z)^p)
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz hω n) p

lemma iidList_integrable_max_square {G : Type*} [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (p : PMF G) (F : G → ℝ) (b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ u ∂p.toMeasure, |F u-b| ≤ B) (n : ℕ) :
    Integrable (fun w => (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2) (iidListPMF p n).toMeasure := by
  obtain ⟨Ω,mΩ,μ,X,hX,hLaw,hind,hprob⟩ := exists_iid ℕ p.toMeasure
  let := mΩ
  let := hprob
  let c := ∫ u, F u ∂p.toMeasure
  let Y := fun k ω => F (X k ω)-c
  have hF : Measurable F := measurable_of_countable F
  have hcb : |c-b| ≤ B := abs_mean_sub_le p.toMeasure F hF b B hbound
  have hY (k) : Measurable (Y k) := (hF.comp (hX k)).sub_const c
  have hYB (k) : ∀ᵐ ω ∂μ, |Y k ω| ≤ 2*B := by
    have hb : ∀ᵐ ω ∂μ, |F (X k ω)-b| ≤ B :=
      (hLaw k).ae_iff (by fun_prop) |>.mpr hbound
    filter_upwards [hb] with ω hω
    calc |Y k ω| = |(F (X k ω)-b)-(c-b)| := by congr 1; dsimp [Y]; ring
         _ ≤ |F (X k ω)-b|+|c-b| := abs_sub _ _
         _ ≤ 2*B := by linarith
  have hi := integrable_partialSumMax_pow_ae μ Y hY (by positivity) hYB n 2
  have hl := iid_list_hasLaw μ p X hX hLaw hind n
  change Integrable (fun w => (listCenteredMax F c w)^2) (iidListPMF p n).toMeasure
  rw [← hl.map_eq]
  apply (integrable_map_measure (by fun_prop) hl.aemeasurable).mpr
  convert hi using 1
  ext ω
  exact congrArg (fun x : ℝ => x^2) (listCenteredMax_ofFn F c (fun k => X k ω) n)

lemma iidList_max_tail {G : Type*} [MeasurableSpace G]
    [MeasurableSingletonClass G] [Countable G]
    [MeasurableSpace (List G)] [MeasurableSingletonClass (List G)]
    (p : PMF G) (F : G → ℝ) (b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ u ∂p.toMeasure, |F u-b| ≤ B) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (iidListPMF p n).toMeasure.real {w | r ≤ listCenteredMax F (∫ u, F u ∂p.toMeasure) w} ≤
      (4*(n:ℝ)*(∫ u, (F u-b)^2 ∂p.toMeasure))/r^2 := by
  have hi := iidList_integrable_max_square p F b hB hbound n
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := (iidListPMF p n).toMeasure)
    (f := fun w => (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2)
    (Eventually.of_forall fun _ => sq_nonneg _) hi (r^2)
  have he : {w | r^2 ≤ (listCenteredMax F (∫ u, F u ∂p.toMeasure) w)^2} =
      {w | r ≤ listCenteredMax F (∫ u, F u ∂p.toMeasure) w} := by
    ext w
    exact sq_le_sq₀ hr.le (partialSumMax_nonneg _ _)
  rw [he] at hm
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  rw [mul_comm]
  exact hm.trans (iidList_integral_max_square_le p F b hB hbound n)

end DirectionalTransience

end

end

end OAI
