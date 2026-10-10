import Mathlib
import OAI.Probability.GaussianInformation.Kernel.PairReference

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open GaussianTools
lemma log_mixture_lower_linear {p d L : ℕ} (hL : 0 < L)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) (s : Vec d) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hs : ∀ᵐ u ∂ν,u ∈ closedBall s R) (X : Mat p d) (e : Fin p → ℝ)
    (he : ∀ i,|e i| ≤ T) (j : Fin L) :
    -Real.log L-(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-
      (R^2*matEnergy X+(p:ℝ)*T^2)/(r j)^2 ≤
        Real.log (mixture ν r X (applyRows X s+e)) := by
  have hl := local_log_lower hL ν ν (m := 1) (by norm_num) (by simp) r hr X
    (applyRows X s+e) s R hs j
  have hei : Integrable (fun u => energy X (s-u) e) ν := by
    apply continuous_integrable_on_support ν _ s R hs
    unfold energy applyRows; fun_prop
  have henergy : (∫ u,energy X (s-u) e ∂ν) ≤ 2*R^2*matEnergy X+2*(p:ℝ)*T^2 := by
    calc
      _ ≤ ∫ _u,2*R^2*matEnergy X+2*(p:ℝ)*T^2 ∂ν := by
        apply integral_mono_ae hei (integrable_const _)
        filter_upwards [hs] with u hu
        have huv : ‖s-u‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hu
        have hs2 := (sq_le_sq₀ (norm_nonneg _) hR).2 huv
        have he2 : (∑ i,e i^2) ≤ (p:ℝ)*T^2 := by
          calc
            _ ≤ ∑ _i : Fin p,T^2 := Finset.sum_le_sum (fun i _ => by
              simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hT).2 (he i))
            _ = _ := by simp
        have hb := energy_le X (s-u) e
        nlinarith [mul_le_mul_of_nonneg_left hs2 (matEnergy_nonneg X)]
      _ = _ := by simp
  have heq : (∫ u,Real.log (atDensity (r j) X (applyRows X s+e) u) ∂ν)=
      -(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-(∫ u,energy X (s-u) e ∂ν)/(2*(r j)^2) := by
    simp_rw [log_atDensity_shift (hr j)]
    rw [integral_sub (integrable_const _) (hei.div_const _),integral_div]
    simp
  rw [heq,Real.log_one,zero_sub] at hl
  have hb := div_le_div_of_nonneg_right henergy (by positivity : 0 ≤ 2*(r j)^2)
  have hd : (2*R^2*matEnergy X+2*(p:ℝ)*T^2)/(2*(r j)^2)=
      (R^2*matEnergy X+(p:ℝ)*T^2)/(r j)^2 := by ring
  rw [hd] at hb
  linarith

lemma log_mixture_uniform_bound {p d L : ℕ} (hL : 0 < L)
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν] (r : Fin L → ℝ)
    (hr : ∀ j,0 < r j) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : Vec d), (∀ᵐ u ∂ν,u ∈ closedBall s R) →
      ∀ (X : Mat p d) (e : Fin p → ℝ), (∀ i,|e i| ≤ T) →
        |Real.log (mixture ν r X (applyRows X s+e))| ≤ M*(1+matEnergy X) := by
  let j : Fin L := ⟨0,hL⟩
  let a := -Real.log L-(p:ℝ)*Real.log (r j)-(p:ℝ)/2*Real.log (2*Real.pi)-(p:ℝ)*T^2/(r j)^2
  let b := R^2/(r j)^2
  let c := Real.log ((L:ℝ)⁻¹*∑ j,densityBound p (r j))
  let M := |a|+b+|c|
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  intro s hs X e he
  have hl := log_mixture_lower_linear hL ν r hr s hR hT hs X e he j
  have hu := Real.log_le_log (mixture_pos hL ν r hr X (applyRows X s+e)) (mixture_upper ν r hr X (applyRows X s+e))
  have hl' : a-b*matEnergy X ≤ Real.log (mixture ν r X (applyRows X s+e)) := by
    dsimp [a,b]; convert hl using 1; ring
  have hu' : Real.log (mixture ν r X (applyRows X s+e)) ≤ c := hu
  apply abs_le.mpr
  have hm := matEnergy_nonneg X
  have hmb : b ≤ M := by dsimp [M]; linarith [abs_nonneg a,abs_nonneg c]
  have hab := neg_abs_le a
  have hcb := le_abs_self c
  have hmul := mul_le_mul_of_nonneg_right hmb hm
  dsimp [M] at hM hmb ⊢
  constructor <;> nlinarith [abs_nonneg a,abs_nonneg c,mul_nonneg (abs_nonneg a) hm,mul_nonneg (abs_nonneg c) hm]
end ReferenceGaussian

end OAI
