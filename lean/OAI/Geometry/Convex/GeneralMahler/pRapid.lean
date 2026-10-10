import OAI.Geometry.Convex.GeneralMahler.CDF
import OAI.Geometry.Convex.GeneralMahler.Rapid

namespace OAI
/-! Scalar tail estimates near §02. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real Metric
open scoped ENNReal NNReal Topology
namespace GeneralMahler

lemma rapid_exp_sq {c : ℝ} (hc : 0 < c) :
    rapid (fun t:ℝ => Real.exp (-(c*t^2))) := by
  intro n
  have Hb : ∀ y:ℝ, -c*y^2 + n*y ≤ (n:ℝ)^2/(4*c) := by
    intro y
    apply (le_div_iff₀ (by positivity : 0 < 4*c)).mpr
    nlinarith [sq_nonneg ((n:ℝ)-2*c*y)]
  use Real.exp ((n:ℝ)^2/(4*c)), exp_nonneg _
  intro t
  rw [Real.norm_eq_abs,abs_of_pos (exp_pos _),Real.norm_eq_abs]
  have ht : 1+|t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
  apply le_trans (mul_le_mul_of_nonneg_left (show (1+|t|)^n ≤ _ from pow_le_pow_left₀ (by positivity) ht _) (exp_nonneg _))
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [sq_abs] using Hb |t|

namespace rapid
variable {E : Type*} [NormedAddCommGroup E] {f g : E → ℝ}
lemma product (hf : rapid f) (hg : PolyBound g) : rapid (fun x => f x*g x) :=
  fun n => by
    obtain ⟨C,m,hc,h₁⟩ := hg
    obtain ⟨D,hd,h₂⟩ := hf (m+n)
    use D*C, by positivity
    intro x
    calc
      _ ≤ ‖f x‖*(C*(1+‖x‖)^m)*(1+‖x‖)^n := by rw [norm_mul]; gcongr; apply h₁
      _ = ‖f x‖*(1+‖x‖)^(m+n)*C := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (h₂ _) hc
lemma mono (hf : rapid f) (h : ∀ x, ‖g x‖ ≤ ‖f x‖) : rapid g := by
  intro n
  obtain ⟨c,hc,h₁⟩ := hf n
  exact ⟨c,hc,fun x => le_trans (mul_le_mul_of_nonneg_right (h x) (by positivity)) (h₁ x)⟩
lemma tail_limit {f : ℝ → ℝ} (h : rapid f) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨c,hc,h₁⟩ := h 1
  simp only [pow_one] at h₁
  apply squeeze_zero_norm'
    (a := fun t => c*(1+t)⁻¹) ?_
  · have htop : Tendsto (fun t : ℝ => 1+t) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
    have he : Tendsto (fun t => c*(1+t)⁻¹) atTop (𝓝 (c*(0:ℝ))) := tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp htop)
    simpa using he
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa [Real.norm_of_nonneg hx.le] using h₁ x
lemma integrable_real {f : ℝ → ℝ} (h : rapid f)
    (hm : Measurable f) : Integrable f :=
  mixed_integrable_left (mixed.of_rapid h) (0:ℝ) hm.aestronglyMeasurable
end rapid

namespace Layers
lemma rapid_phi : rapid phi := by
  have hp := (rapid_exp_sq (show 0<(1/2:ℝ) by norm_num)).product
    (PolyBound.const (X := ℝ) (√(2*π))⁻¹)
  convert hp using 1
  ext x; rw [phi_apply]; ring_nf

lemma p_small :
    ∃ C > (0:ℝ), ∀ s ≥ (0 : ℝ), p (-s) ≤ phi s * C := by
  have H := phi_pos 1
  use 1+(phi 1)⁻¹, by positivity
  intro s hs
  rcases le_total s 1 with h|h
  · have h₁ : phi 1 ≤ phi s := by
      simp_rw [phi_apply]; gcongr
    have h₂ : 1 ≤ phi s / phi 1 := (le_div_iff₀ H).mpr (by simpa using h₁)
    have h₃ := p_lt_one (-s)
    rw [div_eq_mul_inv] at h₂
    nlinarith [phi_pos s]
  · have h' := a_pos (-s)
    rw [a, neg_phi] at h'
    nlinarith [p_pos (-s),phi_pos s, inv_pos.mpr H]

def st (s : ℝ) := if 0 ≤ s then (1:ℝ) else 0
@[fun_prop] lemma measurable_st : Measurable st :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma rapid_p : rapid (fun s => p s-st s) := by
  obtain ⟨C,hc,h⟩ := p_small
  have he : rapid (fun x => phi x*C) := rapid_phi.product (PolyBound.const C)
  apply he.mono
  intro s
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (by apply mul_nonneg (phi_pos s).le hc.le)]
  unfold st; split_ifs with hh
  · rw [abs_of_nonpos (by linarith [p_lt_one s])]
    linarith [neg_p s,h s hh]
  · rw [sub_zero,abs_of_pos (p_pos s)]
    simpa only [neg_neg, neg_phi] using h (-s) (by linarith)
lemma poly_a : PolyBound a := by
  have h₁ : PolyBound phi := PolyBound.of_bound (√(2*π))⁻¹ (fun x => by
    rw [Real.norm_of_nonneg (phi_pos _).le]; exact phi_bdd _)
  have h₂ : PolyBound p := PolyBound.of_bound 1 (fun x => by
    rw [Real.norm_of_nonneg (p_pos _).le]; exact (p_lt_one _).le)
  exact h₁.add (PolyBound.id.mul h₂)

-- ratio p/a used in μ tail moment proof
lemma ratio_bound : PolyBound (fun x => p x / a x) := by
  obtain ⟨C,hc,h⟩ := p_small
  have h₀ := a_pos 0
  let k := C*exp 4+(a 0)⁻¹
  refine ⟨k,2,by dsimp [k]; positivity,?_⟩
  intro x
  have he : 0 < a x := a_pos x
  rw [Real.norm_of_nonneg (div_nonneg (p_pos _).le he.le)]
  rcases le_total x 0 with hx|hx
  · have h1 := a_low (-x) (by linarith)
    have h2 := h (-x) (by linarith)
    simp only [neg_neg,neg_phi] at h1 h2
    have hp : 0 < 1 + -x := by linarith
    apply le_trans _ (show C*exp 4*(1+ -x)^2 ≤ k*(1+‖x‖)^2 by
      rw [Real.norm_eq_abs,abs_of_nonpos hx]; unfold k; gcongr; simp [h₀.le])
    rw [div_le_iff₀ he]
    have he' : phi x ≤ ((1+ -x)^2*exp 4)*a x := by
      rw [Real.exp_neg (4:ℝ)] at h1
      have hv := Real.exp_pos (4:ℝ)
      field_simp at h1
      linarith
    apply h2.trans
    have hu := mul_le_mul_of_nonneg_right he' hc.le
    linarith
  · have h' : p x / a x ≤ 1/a 0 := by
      gcongr
      · exact (p_lt_one _).le
      · exact a_mono.monotone hx
    apply h'.trans
    have hr : 0 ≤ C*exp 4 := by positivity
    have hv := norm_nonneg x
    dsimp only [k]; rw [one_div]
    have hd : 1 ≤ (1+‖x‖)^2 := by nlinarith
    nlinarith [inv_pos.mpr h₀]
end Layers
end GeneralMahler

end

end OAI
