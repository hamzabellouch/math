import OAI.Analysis.HenonEmden.OriginVirial

namespace OAI

section SymmetricVirial

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE Cutoff

lemma radial_gradient_pair {n : ℕ} (x y : Space n) :
    (newtonDenom n)⁻¹*(eta n x*kernelDir x (x-y)+eta n y*kernelDir y (y-x)) =
      (2-(n:ℝ))*newtonKernel n (x,y)*fluxFactor n (x,y) := by
  by_cases hxy : x=y
  · subst y
    simp only [sub_self,kernelDir,inner_zero_left,mul_zero,zero_add,fluxFactor,zero_div]
  have hr : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have he : ‖x-y‖^(-(n:ℝ)) = ‖x-y‖^(2-(n:ℝ))/‖x-y‖^2 := by
    rw [← Real.rpow_two,← Real.rpow_sub hr]
    congr 1; ring
  simp only [kernelDir,finrank_euclideanSpace_fin,norm_sub_rev y x,he,newtonKernel,fluxFactor,X,
    inner_sub_right,real_inner_smul_right]
  rw [show y-x=-(x-y) by abel,inner_neg_left]
  ring

lemma IsSolution.integrable_fluxFactor {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    Integrable (fluxFactor n) (interaction (source u q B) (source v p A)) := by
  have hn3 := h.dimension_ge_three hn
  have hfm := measurable_source h.continuous_u q B
  have hgm := measurable_source h.continuous_v p A
  have hf0 := source_nonneg (fun x => (h.positive_u x).le) q B
  have hg0 := source_nonneg (fun x => (h.positive_v x).le) p A
  apply (integrable_interaction_iff hn3 hfm hgm hf0 hg0 _).mpr
  have hi := ((h.integrable_joint_radial_gradient hn hp hq).add
    (h.swap.integrable_joint_radial_gradient hn hq hp).swap).const_mul ((newtonDenom n)⁻¹/(2-(n:ℝ)))
  apply hi.congr
  exact ae_of_all _ (fun z => by
    dsimp only [Function.comp_def,Prod.swap,Pi.add_apply]
    have he := radial_gradient_pair z.1 z.2
    have hn0 : 2-(n:ℝ) ≠ 0 := by
      have hh : (3:ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    have hh := congrArg (fun a : ℝ => source u q B z.1*source v p A z.2*a/(2-(n:ℝ))) he
    field_simp [hn0] at hh ⊢
    nlinarith [hh])

lemma IsSolution.integral_radial_pair {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫ x, eta n x*source u q B x*dir u x x)+(∫ x, eta n x*source v p A x*dir v x x) =
      (2-(n:ℝ))*(∫ z, fluxFactor n z ∂interaction (source u q B) (source v p A)) := by
  rw [h.integral_eta_source_radialDir hn hp hq,h.swap.integral_eta_source_radialDir hn hq hp,
    ← integral_prod_swap (fun z : Space n × Space n => eta n z.1*source v p A z.1*
        (kernelDir z.1 (z.1-z.2)*source u q B z.2))]
  have hi := (h.swap.integrable_joint_radial_gradient hn hq hp).swap
  simp only [Function.comp_def] at hi
  rw [← mul_add,← integral_add (h.integrable_joint_radial_gradient hn hp hq) hi]
  rw [integral_interaction (h.dimension_ge_three hn) (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) (source_nonneg (fun x => (h.positive_u x).le) q B)
    (source_nonneg (fun x => (h.positive_v x).le) p A),← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only [Prod.swap]
    have he := congrArg (fun a : ℝ => source u q B z.1*source v p A z.2*a) (radial_gradient_pair z.1 z.2)
    nlinarith [he])

lemma IsSolution.symmetric_virial {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ((n:ℝ)+B)/(q+1)*weightedEnergy (eta n) u q B+
      ((n:ℝ)+A)/(p+1)*weightedEnergy (eta n) v p A-
      ((q+1)⁻¹*weightedEnergy (w n) u q B+(p+1)⁻¹*weightedEnergy (w n) v p A) =
      ((n:ℝ)-2)*(∫ z, fluxFactor n z ∂interaction (source u q B) (source v p A)) := by
  have hf := h.weighted_virial hn hp hq
  have hg := h.swap.weighted_virial hn hq hp
  have hpair := h.integral_radial_pair hn hp hq
  have hp1 : p+1 ≠ 0 := by positivity
  have hq1 : q+1 ≠ 0 := by positivity
  field_simp
  linear_combination (p+1)*hf+(q+1)*hg-(p+1)*(q+1)*hpair

end HenonLaneEmden
end
end SymmetricVirial

end OAI
