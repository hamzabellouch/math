import OAI.Analysis.HenonEmden.SymmetricVirial

namespace OAI

section LocalizationIntegral

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

@[fun_prop] lemma measurable_localError (n : ℕ) : Measurable (localError : Space n × Space n → ℝ) := by
  unfold localError
  have hη := (continuous_eta n (E := Space n)).measurable
  have hw := (continuous_w n (E := Space n)).measurable
  fun_prop
lemma localError_nonneg {n : ℕ} (z : Space n × Space n) : 0 ≤ localError z := add_nonneg (abs_nonneg _) (abs_nonneg _)
lemma closeConstant_nonneg (n : ℕ) : 0 ≤ closeConstant n := by
  obtain ⟨hD,hS,hW⟩ := constants_nonneg n
  unfold closeConstant; positivity
lemma farLocalConstant_nonneg (n : ℕ) : 0 ≤ farLocalConstant n := by
  have := (constants_nonneg n).1
  unfold farLocalConstant; positivity

def localFarSum {n : ℕ} (δ : ℝ) (z : Space n × Space n) : ℝ :=
  farWeight δ (N n-1:ℕ) z+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z+
    farWeight δ (N n-1:ℕ) z.swap+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z.swap
lemma localFarSum_nonneg {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (z : Space n × Space n) : 0 ≤ localFarSum δ z := by
  unfold localFarSum
  exact add_nonneg (add_nonneg (add_nonneg (farWeight_nonneg _ _ _) (mul_nonneg (inv_nonneg.mpr hδ)
    (farWeight_nonneg _ _ _))) (farWeight_nonneg _ _ _)) (mul_nonneg (inv_nonneg.mpr hδ) (farWeight_nonneg _ _ _))
lemma localError_global {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/4)
    {z : Space n × Space n} (hne : z.1 ≠ z.2) :
    localError z ≤ closeConstant n*δ*(eta n z.1+eta n z.2)+farLocalConstant n*localFarSum δ z := by
  by_cases hc : 0 < pairGap z ∧ ‖z.1-z.2‖ ≤ δ*pairGap z^(m n)
  · exact (localError_close hn hδ.le hδ1 hc.1 hc.2 hne).trans
      (le_add_of_nonneg_right (mul_nonneg (farLocalConstant_nonneg n) (localFarSum_nonneg hδ.le z)))
  · exact (localError_far hδ hne hc).trans
      (le_add_of_nonneg_left (mul_nonneg (mul_nonneg (closeConstant_nonneg n) hδ.le)
        (add_nonneg (eta_nonneg n _) (eta_nonneg n _))))

def localizationConstant (n : ℕ) (p q A B δ : ℝ) : ℝ :=
  farLocalConstant n*(1+δ⁻¹)*(farConstant n p q A B δ+farConstant n q p B A δ)
lemma localizationConstant_nonneg {n : ℕ} (p q A B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ localizationConstant n p q A B δ := by
  unfold localizationConstant
  exact mul_nonneg (mul_nonneg (farLocalConstant_nonneg n) (by positivity))
    (add_nonneg (farConstant_nonneg _ _ _ _ hδ) (farConstant_nonneg _ _ _ _ hδ))

lemma IsSolution.localFarSum_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (localFarSum δ) (interaction (source u q B) (source v p A)) ∧
    (∫ z, localFarSum δ z ∂interaction (source u q B) (source v p A)) ≤
      (1+δ⁻¹)*(farConstant n p q A B δ+farConstant n q p B A δ) := by
  have h1 := h.farWeight_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).1
  have h2 := h.farWeight_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).2.1
  have h3 := h.farWeight_swap_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).1
  have h4 := h.farWeight_swap_bound hn hp hq hδ hδ1 (cutoff_far_exponents n).2.1
  have h12 : Integrable (fun z => farWeight δ (N n-1:ℕ) z+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z) _ := h1.1.add (h2.1.const_mul _)
  have h123 : Integrable (fun z => farWeight δ (N n-1:ℕ) z+δ⁻¹*farWeight δ ((N n:ℝ)-(m n:ℝ)) z+farWeight δ (N n-1:ℕ) z.swap) _ := h12.add h3.1
  refine ⟨h123.add (h4.1.const_mul _),?_⟩
  unfold localFarSum
  rw [integral_add h123 (h4.1.const_mul _),
    integral_add h12 h3.1,integral_add h1.1 (h2.1.const_mul _),
    integral_const_mul,integral_const_mul]
  have hh := add_le_add (add_le_add (add_le_add h1.2 (mul_le_mul_of_nonneg_left h2.2 (inv_nonneg.mpr hδ.le))) h3.2)
    (mul_le_mul_of_nonneg_left h4.2 (inv_nonneg.mpr hδ.le))
  exact hh.trans_eq (by ring)

lemma IsSolution.localError_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) :
    Integrable localError (interaction (source u q B) (source v p A)) ∧
    (∫ z, localError z ∂interaction (source u q B) (source v p A)) ≤
      closeConstant n*δ*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+localizationConstant n p q A B δ := by
  have hηf := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hηg := h.weight_right hn hp (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hfar := h.localFarSum_bound hn hp hq hδ (by linarith)
  have hηi : Integrable (fun z : Space n × Space n => eta n z.1+eta n z.2) _ := hηf.1.add hηg.1
  have hi : Integrable (fun z : Space n × Space n => closeConstant n*δ*(eta n z.1+eta n z.2)+farLocalConstant n*localFarSum δ z) _ :=
    (hηi.const_mul _).add (hfar.1.const_mul _)
  have hb : ∀ᵐ z ∂interaction (source u q B) (source v p A), localError z ≤
      closeConstant n*δ*(eta n z.1+eta n z.2)+farLocalConstant n*localFarSum δ z :=
    (interaction_ae_ne (by omega : 1 ≤ n) _ _).mono (fun _ hz => localError_global (by omega) hδ hδ1 hz)
  have he : Integrable localError (interaction (source u q B) (source v p A)) := hi.mono'
    (measurable_localError n).aestronglyMeasurable (hb.mono (fun z hz => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (localError_nonneg z)] using hz))
  refine ⟨he,(integral_mono_ae he hi hb).trans ?_⟩
  rw [integral_add (hηi.const_mul _) (hfar.1.const_mul _),integral_const_mul,
    integral_const_mul,integral_add hηf.1 hηg.1,hηf.2,hηg.2]
  calc
    _ ≤ closeConstant n*δ*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+
        farLocalConstant n*((1+δ⁻¹)*(farConstant n p q A B δ+farConstant n q p B A δ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hfar.2 (farLocalConstant_nonneg n))
    _ = _ := by unfold localizationConstant; ring

end HenonLaneEmden
end
end LocalizationIntegral

end OAI
