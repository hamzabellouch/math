import OAI.Analysis.HenonEmden.NearLocalization

namespace OAI

section FarInteraction

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff

def farWeight {n : ℕ} (δ j : ℝ) (z : Space n × Space n) : ℝ :=
  if 0 < d z.1 ∧ δ*d z.1^(m n) ≤ ‖z.1-z.2‖ then d z.1^j else 0

@[fun_prop] lemma measurable_farWeight (n : ℕ) (δ j : ℝ) : Measurable (farWeight (n:=n) δ j) := by
  unfold farWeight
  have hd : Continuous (fun z : Space n × Space n => d z.1) := continuous_d.comp continuous_fst
  have ht : Continuous (fun z : Space n × Space n => δ*d z.1^(m n)) := continuous_const.mul (hd.pow _)
  have hs : Continuous (fun z : Space n × Space n => ‖z.1-z.2‖) := (continuous_fst.sub continuous_snd).norm
  exact (hd.measurable.pow_const j).ite ((isOpen_lt continuous_const hd).measurableSet.inter
    (isClosed_le ht hs).measurableSet) measurable_const

lemma farWeight_nonneg {n : ℕ} (δ j : ℝ) (z : Space n × Space n) : 0 ≤ farWeight δ j z := by
  unfold farWeight; split_ifs
  · exact Real.rpow_nonneg (d_nonneg z.1) j
  · exact le_rfl

lemma far_power_bound {n : ℕ} {δ r j : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    r^j*(δ*r^(m n))^(2-(n:ℝ)) ≤ δ^(2-(n:ℝ)) := by
  rw [Real.mul_rpow hδ.le (pow_nonneg hr.le _),← Real.rpow_natCast r (m n),← Real.rpow_mul hr.le,
    mul_left_comm,← Real.rpow_add hr]
  exact mul_le_of_le_one_right (by positivity) (Real.rpow_le_one hr.le hr1 hj)

lemma IsSolution.truncated_newton_bound {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    {x : Space n} (hx : ‖x‖ ≤ 4) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))) ≤
      ENNReal.ofReal ((newtonDenom n)⁻¹*(sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)+
        uniformTailConstant n p q A B)*l^(2-(n:ℝ))) := by
  have hd := newtonDenom_pos (h.dimension_ge_three hn)
  have hgm := measurable_source h.continuous_v p A
  have hs : MeasurableSet {y : Space n | l ≤ ‖x-y‖} := (isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet
  have he : (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) ∂sourceMeasure v p A) =
      ∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) := by
    rw [← lintegral_indicator hs,lintegral_sourceMeasure h.continuous_v p A (by fun_prop)]
    rw [← lintegral_indicator hs]
    apply lintegral_congr
    intro y
    by_cases hy : l ≤ ‖x-y‖ <;> simp [hy]
  simp_rw [newtonKernel,ENNReal.ofReal_mul (inv_nonneg.mpr hd.le),mul_left_comm (ENNReal.ofReal (source v p A _))]
  rw [lintegral_const_mul _ (by fun_prop),← he]
  have hh := mul_le_mul (le_refl (ENNReal.ofReal ((newtonDenom n)⁻¹))) (h.uniform_g_truncated hn hp hq hx hl hl1) bot_le bot_le
  convert hh using 1; first | rfl | rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le)]; congr 1; ring

def truncatedConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  max ((newtonDenom n)⁻¹*(sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)+
    uniformTailConstant n p q A B)) 0

def farConstant (n : ℕ) (p q A B δ : ℝ) : ℝ :=
  truncatedConstant n p q A B*δ^(2-(n:ℝ))*
    max (sourceConstant n q p B A*2^((n:ℝ)-2-alpha q p B A)) 0

lemma truncatedConstant_nonneg (n : ℕ) (p q A B : ℝ) : 0 ≤ truncatedConstant n p q A B := le_max_right _ _
lemma farConstant_nonneg {n : ℕ} (p q A B : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ farConstant n p q A B δ := by
  unfold farConstant
  exact mul_nonneg (mul_nonneg (truncatedConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hδ _)) (le_max_right _ _)

lemma IsSolution.far_inner_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) (x : Space n) :
    (∫⁻ y, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))*
      ENNReal.ofReal (farWeight δ j (x,y))) ≤
      (ball (0:Space n) 2).indicator (fun _ => ENNReal.ofReal (truncatedConstant n p q A B*δ^(2-(n:ℝ)))) x := by
  have hgm := measurable_source h.continuous_v p A
  by_cases hx : 0 < d x
  · have hx2 : x ∈ ball (0:Space n) 2 := mem_ball_zero_iff.mpr ((d_pos_iff x).mp hx)
    rw [indicator_of_mem hx2]
    let l := δ*d x^(m n)
    have hl : 0 < l := mul_pos hδ (pow_pos hx _)
    have hl1 : l ≤ 1 := (mul_le_of_le_one_left (pow_nonneg hx.le _) hδ1).trans
      (pow_le_one₀ hx.le (d_le_one x))
    have hs : MeasurableSet {y : Space n | l ≤ ‖x-y‖} :=
      (isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet
    have he : (∫⁻ y, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))*
        ENNReal.ofReal (farWeight δ j (x,y))) =
        ENNReal.ofReal (d x^j)*(∫⁻ y in {y | l ≤ ‖x-y‖},
          ENNReal.ofReal (source v p A y)*ENNReal.ofReal (newtonKernel n (x,y))) := by
      rw [← lintegral_const_mul _ (by fun_prop),← lintegral_indicator hs]
      apply lintegral_congr
      intro y
      by_cases hy : l ≤ ‖x-y‖ <;> simp [farWeight,hx,hy,l]
      ring
    rw [he]
    have hb := (h.truncated_newton_bound hn hp hq (by have hh := mem_ball_zero_iff.mp hx2; linarith) hl hl1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ 0) (Real.rpow_nonneg hl.le (2-(n:ℝ)))))
    have hh := mul_le_mul (le_refl (ENNReal.ofReal (d x^j))) hb bot_le bot_le
    apply hh.trans
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le j)]
    apply ENNReal.ofReal_le_ofReal
    convert mul_le_mul_of_nonneg_left (far_power_bound hδ hx (d_le_one x) hj)
      (truncatedConstant_nonneg n p q A B) using 1; first | rfl | dsimp [truncatedConstant,l]; ring
  · have hx2 : x ∉ ball (0:Space n) 2 := by simpa only [mem_ball_zero_iff,← d_pos_iff x] using hx
    simp only [farWeight,hx,false_and,ite_false,ENNReal.ofReal_zero,mul_zero,lintegral_zero,
      indicator_of_notMem hx2]
    exact le_rfl

lemma IsSolution.far_interaction_bound {n : ℕ} (hn : 2 ≤ n) {p q A B δ j : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hj : 0 ≤ j+(m n:ℝ)*(2-(n:ℝ))) :
    (∫⁻ z, ENNReal.ofReal (farWeight δ j z) ∂interaction (source u q B) (source v p A)) ≤
      ENNReal.ofReal (farConstant n p q A B δ) := by
  have hfm := measurable_source h.continuous_u q B
  have hgm := measurable_source h.continuous_v p A
  rw [lintegral_interaction hfm hgm (by fun_prop),lintegral_prod _ (by fun_prop)]
  have heq (x : Space n) : (∫⁻ y, ENNReal.ofReal (source u q B x)*
      (ENNReal.ofReal (source v p A y)*(ENNReal.ofReal (newtonKernel n (x,y))*ENNReal.ofReal (farWeight δ j (x,y))))) =
      ENNReal.ofReal (source u q B x)*(∫⁻ y,
      ENNReal.ofReal (source v p A y)*(ENNReal.ofReal (newtonKernel n (x,y))*ENNReal.ofReal (farWeight δ j (x,y)))) :=
    lintegral_const_mul _ (by fun_prop)
  simp_rw [mul_assoc,heq]
  have hb := lintegral_mono (μ := volume) (fun x => mul_le_mul (le_refl (ENNReal.ofReal (source u q B x)))
    (h.far_inner_bound hn hp hq hδ hδ1 hj x) bot_le bot_le)
  simp only [mul_assoc] at hb
  apply hb.trans
  have he : (∫⁻ x, ENNReal.ofReal (source u q B x)*(ball (0:Space n) 2).indicator
      (fun _ => ENNReal.ofReal (truncatedConstant n p q A B*δ^(2-(n:ℝ)))) x) =
      ENNReal.ofReal (truncatedConstant n p q A B*δ^(2-(n:ℝ)))*sourceMeasure u q B (ball 0 2) := by
    rw [← lintegral_sourceMeasure h.continuous_u q B (measurable_const.indicator measurableSet_ball),
      lintegral_indicator measurableSet_ball,setLIntegral_const]
  rw [he,h.swap.sourceMeasure_ball hn]
  have hm := (h.swap.sourceMass_g_upper hn hq hp (by norm_num : (0:ℝ) < 2)).trans (le_max_left _ 0)
  exact (mul_le_mul (le_refl _) (ENNReal.ofReal_le_ofReal hm) bot_le bot_le).trans_eq
    (by rw [← ENNReal.ofReal_mul (mul_nonneg (truncatedConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hδ.le _))]; rfl)

lemma lintegral_interaction_swap {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.swap ∂interaction f g) = ∫⁻ z, F z ∂interaction g f := by
  change (∫⁻ z, (F ∘ Prod.swap) z ∂interaction f g) = _
  rw [lintegral_interaction hf hg (hF.comp measurable_swap),lintegral_interaction hg hf hF,← lintegral_prod_swap]
  apply lintegral_congr
  intro z
  change ENNReal.ofReal (f z.2)*ENNReal.ofReal (g z.1)*ENNReal.ofReal (newtonKernel n (z.2,z.1))*F z = _
  rw [newtonKernel_symm n z.2 z.1]
  ring

end HenonLaneEmden
end
end FarInteraction

end OAI
