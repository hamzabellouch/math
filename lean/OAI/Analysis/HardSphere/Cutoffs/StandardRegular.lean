import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.RegularTail
import OAI.Analysis.HardSphere.Thermodynamics.CutoffAsymptotics

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace HardSphere.PathCutoff
open Wiener FreeVisits

lemma scalarRegularBound_nonneg {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (c a b D : ℝ) :
    0 ≤ scalarRegularBound C M c a b D := by unfold scalarRegularBound; positivity

lemma regular_root_decay {C M c a b : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun D:ℝ ↦ D*(scalarRegularBound C M c a b D)^(1/3:ℝ)) atTop (𝓝 0) := by
  have ht := (scalarRegularBound_decay (3:ℝ) C M hc ha hb).rpow_const (p:=(3⁻¹:ℝ)) (Or.inr (by positivity))
  rw [Real.zero_rpow (by norm_num : (3⁻¹:ℝ)≠0)] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with D hD
  rw [Real.mul_rpow (Real.rpow_nonneg hD _) (scalarRegularBound_nonneg hC hM c a b D),
    ←Real.rpow_mul hD]
  norm_num

lemma free_regular_standard_tail {c : ℝ} {M : ℝ≥0∞} (hM : M≠⊤)
    (htail : ∀R:ℝ,0 ≤ R→wiener {w | R ≤ ‖w‖} ≤ M*ENNReal.ofReal (Real.exp (-c*R^2)))
    {L : Length} {r τ D C a b : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτr : τ ≤ r^2)
    (hc : 0 ≤ c) (hD : 1 ≤ D) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hm : 0 < m) (hmlo : a*D^2 ≤ (m:ℝ)) (hmhi : (m:ℝ) ≤ C*D^2)
    (hhT : D⁻¹ < (m:ℝ)*τ) (X : Configuration 1 L) :
    coordinateWiener 1 {w | ¬Regular m r (D^(1/12:ℝ)) (meanCost+1)
      (splitTime (D⁻¹) ((m:ℝ)*τ-D⁻¹) (by positivity) (sub_pos.mpr hhT))
      (b*D^(-(1/3:ℝ))/8) (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
        ENNReal.ofReal (scalarRegularBound C (3*M.toReal) c a b D) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hh := free_regular_tail htail hr hτ hτr (Real.rpow_nonneg hD0.le (1/12:ℝ)) m hm
    (by positivity : 0 < D⁻¹) hhT (by positivity : 0 ≤ b*D^(-(1/3:ℝ))/8) X
  apply hh.trans
  have hfinite : (m:ℝ≥0∞)*(3*M*ENNReal.ofReal (Real.exp (-c*(D^(1/12:ℝ)/36)^2)))+
      ENNReal.ofReal (Real.exp (-(m:ℝ)/((1+D^(1/12:ℝ))^3)))+
      2*(3*M*ENNReal.ofReal (Real.exp (-c*((b*D^(-(1/3:ℝ))/8)/(36*Real.sqrt (D⁻¹)))^2)))≠⊤ := by finiteness
  apply (ENNReal.le_ofReal_iff_toReal_le hfinite (scalarRegularBound_nonneg hC (by positivity) c a b D)).mpr
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact regularScale_majorant (M:=3*M.toReal) (b:=b) hD hC (by positivity) hc ha hmlo hmhi

end HardSphere.PathCutoff

end
end

end

end OAI
