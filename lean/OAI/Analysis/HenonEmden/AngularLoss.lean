import OAI.Analysis.HenonEmden.AngularMeasurability

namespace OAI

section AngularLoss

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

def sourceBallConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  max (sourceConstant n p q A B*4^((n:ℝ)-2-alpha p q A B)) 0+
    max (sourceConstant n q p B A*4^((n:ℝ)-2-alpha q p B A)) 0
lemma sourceBallConstant_nonneg (n : ℕ) (p q A B : ℝ) : 0 ≤ sourceBallConstant n p q A B :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)
lemma sourceBallConstant_swap (n : ℕ) (p q A B : ℝ) :
    sourceBallConstant n q p B A=sourceBallConstant n p q A B := by unfold sourceBallConstant; ring

lemma IsSolution.source_g_ball_bound {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫⁻ x in ball (0:Space n) 4, ENNReal.ofReal (source v p A x)) ≤
      ENNReal.ofReal (sourceBallConstant n p q A B) := by
  have hs := h.sourceMeasure_ball hn 4
  rw [sourceMeasure,withDensity_apply _ measurableSet_ball] at hs
  rw [hs]
  apply ENNReal.ofReal_le_ofReal
  apply (h.sourceMass_g_upper hn hp hq (by norm_num : (0:ℝ)<4)).trans
  exact (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))

lemma IsSolution.u_mass_two_bound {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫⁻ x in ball (0:Space n) 2, ENNReal.ofReal (u x)) ≤
      ENNReal.ofReal (max (uniformMassConstant n p q A B) 0) := by
  have hi : IntegrableOn u (ball (0:Space n) 4) :=
    (h.continuous_u.continuousOn.integrableOn_compact (isCompact_closedBall _ 4)).mono_set ball_subset_closedBall
  apply (lintegral_mono_set (ball_subset_ball (by norm_num : (2:ℝ) ≤ 4))).trans
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => (h.positive_u x).le))]
  exact ENNReal.ofReal_le_ofReal ((h.uniform_u_mass hn hp hq).trans (le_max_left _ _))

lemma IsSolution.angular_loss_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ P : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hP : 0 < P) :
    (∫⁻ e : sphere (0:Space n) 1, lossIntegral u (source u q B) κ δ e ∂volume.toSphere) ≤
      ENNReal.ofReal (lossCoefficient (volume : Measure (Space n)) κ δ (sourceBallConstant n p q A B) P*
        weightedEnergy (eta n) u q B+
        lowLevelConstant n*P*max (uniformMassConstant n p q A B) 0) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hf := measurable_source h.continuous_u q B
  have hu := h.continuous_u.measurable
  have hu0 := fun x => (h.positive_u x).le
  have hfo := isOpen_source_subgraph h.regular_u h.positive_u q B
  rw [lintegral_angular_loss (by omega) hκ hκ1 hf hu hu0 hfo]
  have hm := h.swap.source_g_ball_bound hn hq hp
  rw [sourceBallConstant_swap] at hm
  have hh := lintegral_averagedLoss_bound volume hf hu hfo (source_nonneg hu0 q B) hu0
    hκ hκ1 hδ hδ1 (sourceBallConstant_nonneg n p q A B) hP hm
  simp only [finrank_euclideanSpace_fin] at hh
  apply hh.trans
  have hc := lossCoefficient_nonneg (volume : Measure (Space n)) hκ.le hδ.le
    (sourceBallConstant_nonneg n p q A B) hP.le
  have hE := weightedEnergyN_nonneg (eta_nonneg n) hu0 (q:=q) (B:=B)
  have hl : 0 ≤ lowLevelConstant n*P := mul_nonneg (lowLevelConstant_nonneg n) hP.le
  have heq := h.weightedEnergyN_eq hn (continuous_eta n) (compactSupport_eta n) (eta_nonneg n)
  change weightedEnergyN (eta n) u q B=ENNReal.ofReal (weightedEnergy (eta n) u q B) at heq
  change ENNReal.ofReal _ * weightedEnergyN (eta n) u q B + _ ≤ _
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal _*ENNReal.ofReal (weightedEnergy (eta n) u q B)+
        ENNReal.ofReal (lowLevelConstant n*P)*ENNReal.ofReal (max (uniformMassConstant n p q A B) 0) :=
      add_le_add le_rfl (mul_le_mul le_rfl (h.u_mass_two_bound hn hp hq) bot_le bot_le)
    _ = _ := by rw [← ENNReal.ofReal_mul hc,← ENNReal.ofReal_mul hl,
      ← ENNReal.ofReal_add (mul_nonneg hc hE) (mul_nonneg hl (le_max_right _ _))]

end HenonLaneEmden
end
end AngularLoss

end OAI
