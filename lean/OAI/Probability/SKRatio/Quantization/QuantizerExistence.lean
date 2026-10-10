import Mathlib
import OAI.Probability.SKRatio.Quantization.BinStability
import OAI.Probability.SKRatio.Quantization.TanhEnds
import OAI.Probability.SKRatio.Quantization.Quantizer

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression

lemma quantizer_integrable_square {R : ℝ} (hR : 0<R) {N : ℕ} (hN : 0<N)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable (fun x : ℝ => x^2) μ) :
    Integrable (fun x => (x-gridQuant R N x)^2) μ := by
  apply ((integrable_const ((2*R/N)^2)).add (integrable_squareTail hi R)).mono'
    ((measurable_id.sub (measurable_gridQuant hR hN)).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact gridQuant_square_error hR hN x)

theorem quantizer_exists
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    (hX : ExponentialSquareTails ρ X)
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hi : Integrable (fun x : ℝ => x^2) μ)
    {δ d : ℝ} (hδ : 0<δ) (hd : 0<d) :
    ∃ R : ℝ, ∃ N : ℕ, 0<R ∧ 0<N ∧
      (∀ x, dist (compactWeight x) (compactWeight (gridQuant R N x))<δ) ∧
      (∫ x, (x-gridQuant R N x)^2 ∂μ)<d^2 ∧
      ExponentiallyRare ρ (fun n => {ω | d≤ siteNorm (fun i => X n ω i-gridQuant R N (X n ω i))}) := by
  obtain ⟨Rt,hRt,ht⟩ := hX (d^2/2) (by positivity)
  obtain ⟨Rc,hRc,hc⟩ := tanh_tail_uniform hδ
  have he := (tendsto_integral_squareTail hi).eventually (gt_mem_nhds (by positivity : (0:ℝ)<d^2/4))
  obtain ⟨Ng,hNg⟩ := eventually_atTop.mp he
  let R := max (max Rt Rc) (Ng:ℝ)
  have hR : 0<R := hRc.trans_le ((le_max_right Rt Rc).trans (le_max_left _ _))
  have hRtR : Rt≤R := (le_max_left Rt Rc).trans (le_max_left _ _)
  have hRcR : Rc≤R := (le_max_right Rt Rc).trans (le_max_left _ _)
  have hRg : (Ng:ℝ)≤R := le_max_right _ _
  have hg : (∫ x, squareTail R x ∂μ)<d^2/4 := by
    apply lt_of_le_of_lt (integral_mono (integrable_squareTail hi R) (integrable_squareTail hi Ng)
      (squareTail_antitone hRg))
    exact hNg Ng le_rfl
  let a := min δ (d/2)
  have ha : 0<a := lt_min hδ (half_pos hd)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*R/a)
  have hN0 : 0<N := by
    have hnR : (0:ℝ)<N := (by positivity : (0:ℝ)<2*R/a).trans hN
    exact_mod_cast hnR
  have hmesh : 2*R/(N:ℝ)<a := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hN0)]
    have hh := (div_lt_iff₀ ha).mp hN
    nlinarith only [hh]
  have hmeshd : (2*R/(N:ℝ))^2<d^2/4 := by
    have hh := hmesh.trans_le (min_le_right δ (d/2))
    have h0 : 0≤2*R/(N:ℝ) := by positivity
    nlinarith only [hh,hd,h0]
  refine ⟨R,N,hR,hN0,?_,?_,?_⟩
  · exact gridQuant_compact_error hδ hR hN0 (hmesh.trans_le (min_le_left _ _)) (hc R hRcR)
  · have hle := integral_mono (quantizer_integrable_square hR hN0 hi)
      ((integrable_const ((2*R/(N:ℝ))^2)).add (integrable_squareTail hi R))
      (gridQuant_square_error hR hN0)
    simp only [Pi.add_apply] at hle
    rw [integral_add (integrable_const _) (integrable_squareTail hi R),integral_const] at hle
    simp only [probReal_univ,one_smul] at hle
    linarith [sq_pos_of_pos hd]
  · apply ht.mono
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro ω hω
    change d≤ siteNorm (fun i => X n ω i-gridQuant R N (X n ω i)) at hω
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have h1 : d^2≤(∑ i, (X n ω i-gridQuant R N (X n ω i))^2)/(n:ℝ) := by
      rw [←siteNorm_sq]
      exact (sq_le_sq₀ hd.le (siteNorm_nonneg _)).mpr hω
    have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => gridQuant_square_error hR hN0 (X n ω i))
    have h3 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => squareTail_antitone hRtR (X n ω i))
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h2
    have hh := div_le_div_of_nonneg_right h2 hnR.le
    rw [add_div,mul_div_cancel_left₀ _ (ne_of_gt hnR)] at hh
    have hh' := div_le_div_of_nonneg_right h3 hnR.le
    change d^2/2≤(∑ i, squareTail Rt (X n ω i))/(n:ℝ)
    nlinarith only [h1,hh,hh',hmeshd,sq_nonneg d]

end SKRatio.Bins

end

end OAI
