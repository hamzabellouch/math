import OAI.Analysis.HenonEmden.RealInteraction

namespace OAI

universe uα

section InteractionBounds

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

lemma integrable_integral_le_of_lintegral_le {α : Type uα} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) {C : ℝ} (hC : 0 ≤ C)
    (hb : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal C) :
    Integrable F μ ∧ (∫ x, F x ∂μ) ≤ C := by
  have hf : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable (ae_of_all _ hF0)).mp hf,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hF.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq (ENNReal.toReal_ofReal hC)

lemma IsSolution.lintegral_weight_left {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.1) ∂interaction (source u q B) (source v p A)) =
      ENNReal.ofReal (weightedEnergy χ u q B) := by
  rw [h.interaction_left hn hq hχ.measurable.ennreal_ofReal,← h.weightedEnergyN_eq hn hχ hχc hχ0]
  unfold weightedEnergyN
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg (source_nonneg (fun x => (h.positive_u x).le) q B x) (h.positive_u x).le)]
  congr 1; ring

lemma IsSolution.lintegral_weight_right {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    (∫⁻ z, ENNReal.ofReal (χ z.2) ∂interaction (source u q B) (source v p A)) =
      ENNReal.ofReal (weightedEnergy χ v p A) := by
  rw [h.interaction_right hn hp hχ.measurable.ennreal_ofReal,← h.swap.weightedEnergyN_eq hn hχ hχc hχ0]
  unfold weightedEnergyN
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg (source_nonneg (fun x => (h.positive_v x).le) p A x) (h.positive_v x).le)]
  congr 1; ring

lemma IsSolution.weight_left {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Integrable (fun z => χ z.1) (interaction (source u q B) (source v p A)) ∧
    (∫ z, χ z.1 ∂interaction (source u q B) (source v p A)) = weightedEnergy χ u q B := by
  have he := h.lintegral_weight_left hn hq hχ hχc hχ0
  refine ⟨(integrable_integral_le_of_lintegral_le (hχ.measurable.comp measurable_fst) (fun z => hχ0 z.1)
    (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_u x).le)) he.le).1,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z : Space n × Space n => hχ0 z.1)) (hχ.measurable.comp measurable_fst).aestronglyMeasurable,he,
    ENNReal.toReal_ofReal (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_u x).le))]

lemma IsSolution.weight_right {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v χ : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Integrable (fun z => χ z.2) (interaction (source u q B) (source v p A)) ∧
    (∫ z, χ z.2 ∂interaction (source u q B) (source v p A)) = weightedEnergy χ v p A := by
  have he := h.lintegral_weight_right hn hp hχ hχc hχ0
  refine ⟨(integrable_integral_le_of_lintegral_le (hχ.measurable.comp measurable_snd) (fun z => hχ0 z.2)
    (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_v x).le)) he.le).1,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z : Space n × Space n => hχ0 z.2)) (hχ.measurable.comp measurable_snd).aestronglyMeasurable,he,
    ENNReal.toReal_ofReal (weightedEnergyN_nonneg hχ0 (fun x => (h.positive_v x).le))]

lemma IsSolution.farWeight_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    Integrable (farWeight δ j) (interaction (source u q B) (source v p A)) ∧
    (∫ z, farWeight δ j z ∂interaction (source u q B) (source v p A)) ≤ farConstant n p q A B δ :=
  integrable_integral_le_of_lintegral_le (by fun_prop) (farWeight_nonneg δ j) (farConstant_nonneg p q A B hδ.le)
    (h.far_interaction_bound hn hp hq hδ hδ1 hj)

lemma IsSolution.farWeight_swap_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    Integrable (fun z => farWeight δ j z.swap) (interaction (source u q B) (source v p A)) ∧
    (∫ z, farWeight δ j z.swap ∂interaction (source u q B) (source v p A)) ≤ farConstant n q p B A δ := by
  apply integrable_integral_le_of_lintegral_le ((measurable_farWeight n δ j).comp measurable_swap) (fun z => farWeight_nonneg δ j z.swap)
    (farConstant_nonneg q p B A hδ.le)
  simp only [Function.comp_def]
  rw [lintegral_interaction_swap (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) (measurable_farWeight n δ j).ennreal_ofReal]
  exact h.swap.far_interaction_bound hn hq hp hδ hδ1 hj

lemma cutoff_far_exponents (n : ℕ) :
    0 ≤ ((N n-1:ℕ):ℝ)+(m n:ℝ)*(2-(n:ℝ)) ∧
    0 ≤ ((N n:ℝ)-(m n:ℝ))+(m n:ℝ)*(2-(n:ℝ)) ∧
    0 ≤ ((N n-n:ℕ):ℝ)+(m n:ℝ)*(2-(n:ℝ)) := by
  have hN : 1 ≤ N n := by have := N_ge_two n; omega
  have hNn : n ≤ N n := by unfold N; omega
  rw [Nat.cast_sub hN,Nat.cast_sub hNn]
  simp only [N,m,k,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  constructor <;> (try constructor) <;> nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end HenonLaneEmden
end
end InteractionBounds

end OAI
