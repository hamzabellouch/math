import OAI.Analysis.HenonEmden.LocalizationIntegral

namespace OAI

section AngularBounds

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents

lemma d_w_bound {n : ℕ} (x : Space n) : d x*w n x ≤ 6*(N n:ℝ)*eta n x := by
  rw [w_eq_profile]
  exact gap_wProfile_bound n (norm_nonneg x)

lemma IsSolution.integrable_radialWeight {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    Integrable (fun z : Space n × Space n => w n z.1*radialFactor z) (interaction (source u q B) (source v p A)) := by
  have hi := (h.weight_left hn hq (continuous_w n) (compactSupport_w n) (w_nonneg n)).1
  apply hi.mono' (((continuous_w n).measurable.comp measurable_fst).mul (measurable_radialFactor n)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    dsimp only [Function.comp_def,Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (w_nonneg n _) (radialFactor_bounds z).1)]
    exact mul_le_of_le_one_right (w_nonneg n _) (radialFactor_bounds z).2)

def radialPressure {n : ℕ} (f g : Space n → ℝ) : ℝ :=
  ((n:ℝ)-2)*(∫ z : Space n × Space n, w n z.1*radialFactor z ∂interaction f g)
lemma radialPressure_nonneg {n : ℕ} (hn : 2 ≤ n) (f g : Space n → ℝ) : 0 ≤ radialPressure f g := by
  have hn2 : 0 ≤ (n:ℝ)-2 := by exact_mod_cast (Nat.cast_le.mpr hn : (2:ℝ) ≤ n) |> sub_nonneg.mpr
  exact mul_nonneg hn2 (integral_nonneg (fun z => mul_nonneg (w_nonneg n _) (radialFactor_bounds z).1))

lemma lintegral_angular_interaction_weight {n : ℕ} (hn : 1 ≤ n) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {f g : Space n → ℝ} (_hf : Measurable f) (_hg : Measurable g)
    {G : Space n × Space n → ℝ} (hG : Measurable G) (_hG0 : ∀ z, 0 ≤ G z) :
    (∫⁻ e : sphere (0:Space n) 1, ∫⁻ z, ENNReal.ofReal (weight volume κ e z.1*G z)
      ∂interaction f g ∂volume.toSphere) =
      ∫⁻ z, ENNReal.ofReal (w n z.1*G z) ∂interaction f g := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) =>
      ENNReal.ofReal (weight volume κ z.1 z.2.1*G z.2)) :=
    (((measurable_weight volume hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)).mul (hG.comp measurable_snd)).ennreal_ofReal
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro z
  simp_rw [ENNReal.ofReal_mul (weight_nonneg volume κ _ _)]
  rw [lintegral_mul_const _ (continuous_weight_direction volume κ z.1).measurable.ennreal_ofReal,
    lintegral_cap_weight hn hκ hκ1,← ENNReal.ofReal_mul (w_nonneg n _)]

lemma IsSolution.angular_pressure_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (_hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫⁻ e : sphere (0:Space n) 1, capPressureIntegral (source u q B) (source v p A) κ e ∂volume.toSphere) ≤
      ENNReal.ofReal (radialPressure (source u q B) (source v p A)+
        (12*(N n:ℝ)*((n:ℝ)-2)*κ)*weightedEnergy (eta n) u q B) := by
  have hn2 : 0 ≤ (n:ℝ)-2 := by
    have hh : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hm : Measurable (fun z : Space n × Space n => ((n:ℝ)-2)*(radialFactor z+2*κ*d z.1)) := by
    have hd := (continuous_d (E := Space n)).measurable
    fun_prop
  have hg0 (z : Space n × Space n) : 0 ≤ ((n:ℝ)-2)*(radialFactor z+2*κ*d z.1) :=
    mul_nonneg hn2 (add_nonneg (radialFactor_bounds z).1 (by positivity [d_nonneg z.1]))
  have hb := lintegral_mono (μ := (volume : Measure (Space n)).toSphere) (fun e : sphere (0:Space n) 1 =>
    lintegral_mono (μ := interaction (source u q B) (source v p A)) (fun z => ENNReal.ofReal_le_ofReal
      (show ((n:ℝ)-2)*weight volume κ e z.1*directionalFactor e z ≤ weight volume κ e z.1*(((n:ℝ)-2)*(radialFactor z+2*κ*d z.1)) by
        nlinarith [mul_le_mul_of_nonneg_left (weight_directional_bound (by omega : 1 ≤ n) hκ e z.1 z.2) hn2])))
  change (∫⁻ e : sphere (0:Space n) 1, capPressureIntegral (source u q B) (source v p A) κ e ∂volume.toSphere) ≤ _ at hb
  rw [lintegral_angular_interaction_weight (by omega) hκ hκ1 (measurable_source h.continuous_u q B)
    (measurable_source h.continuous_v p A) hm hg0] at hb
  apply hb.trans
  have he (z : Space n × Space n) : w n z.1*(((n:ℝ)-2)*(radialFactor z+2*κ*d z.1)) ≤
      ((n:ℝ)-2)*(w n z.1*radialFactor z)+(12*(N n:ℝ)*((n:ℝ)-2)*κ)*eta n z.1 := by
    have hh := mul_le_mul_of_nonneg_left (d_w_bound z.1) (show 0 ≤ 2*((n:ℝ)-2)*κ by positivity)
    nlinarith [hh]
  apply (lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (he z))).trans_eq
  have hj := (h.integrable_radialWeight hn hq).const_mul ((n:ℝ)-2)
  have hη := h.weight_left hn hq (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  have hi : Integrable (fun z : Space n × Space n => ((n:ℝ)-2)*(w n z.1*radialFactor z)+(12*(N n:ℝ)*((n:ℝ)-2)*κ)*eta n z.1) _ :=
    hj.add (hη.1.const_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => add_nonneg
    (mul_nonneg hn2 (mul_nonneg (w_nonneg n _) (radialFactor_bounds z).1))
    (mul_nonneg (by positivity) (eta_nonneg n _)))),integral_add hj (hη.1.const_mul _),
    integral_const_mul,integral_const_mul,hη.2]
  rfl

lemma weightedEnergyN_d_w_le {n : ℕ} {u : Space n → ℝ} (hu : Continuous u)
    (hu0 : ∀ x, 0 ≤ u x) (q B : ℝ) :
    weightedEnergyN (fun x => d x*w n x) u q B ≤ ENNReal.ofReal (6*(N n:ℝ))*weightedEnergyN (eta n) u q B := by
  unfold weightedEnergyN
  have hm : Measurable (fun x => ENNReal.ofReal (eta n x*source u q B x*u x)) :=
    (((continuous_eta n).measurable.mul (measurable_source hu q B)).mul hu.measurable).ennreal_ofReal
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 6*(N n:ℝ))]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (d_w_bound x) (source_nonneg hu0 q B x)) (hu0 x)
  nlinarith [hh]

end HenonLaneEmden
end
end AngularBounds

end OAI
