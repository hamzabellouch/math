import Mathlib
import OAI.Probability.SKSupport.Diffusion.FiniteTransition

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat WeakIto Nonuniform
variable {Ω : Type*} [MeasurableSpace Ω]

lemma abs_lipschitz : LipschitzWith (1:ℝ≥0) (abs : ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y

lemma plateau_grid_error_zero (γ : OrderParameter) {a c t : ℝ} (hc0 : 0 ≤ c)
    (ht0 : 0 ≤ t) (hat : a < t) (ht1 : t < 1) (hc : ∀ s ∈ Ioo a 1, extend γ.val s=c) :
    gridError (fun _ => Real.toNNReal (1-t)) (fun _ => ⟨c,hc0⟩) (fun r => extend γ.val (t+r)) 1=0 := by
  simp only [gridError,Finset.sum_range_one,time_zero,time_succ,zero_add,NNReal.coe_zero,
    Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
  have he : (∫ r in (0:ℝ)..(1-t), |c-extend γ.val (t+r)|)=∫ _r in (0:ℝ)..(1-t), (0:ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (sub_nonneg.mpr ht1.le)
    intro r hr
    change |c-extend γ.val (t+r)|=0
    have htr : t+r ∈ Ico (0:ℝ) 1 := ⟨add_nonneg ht0 hr.1.le,by linarith [hr.2]⟩
    have hval : γ.val ⟨t+r,htr⟩=c := by
      simpa only [extend,dite_eq_left htr] using hc (t+r) ⟨by linarith [hr.1],htr.2⟩
    rw [extend,dite_eq_left htr,hval,sub_self,abs_zero]
  change (∫ r in (0:ℝ)..(1-t), |c-extend γ.val (t+r)|)=0
  rw [he,intervalIntegral.integral_zero]

theorem value_on_terminal_plateau (W : BrownianSystem Ω) (γ : OrderParameter) {a c t : ℝ}
    (hc0 : 0 ≤ c) (ht0 : 0 ≤ t) (hat : a < t) (ht1 : t < 1)
    (hc : ∀ s ∈ Ioo a 1, extend γ.val s=c) :
    value W γ t=varianceLogHeat c (1-t) abs := by
  funext x
  rw [varianceLogHeat_eq_logSemigroup_toNNReal measurable_abs]
  let H : ℕ → ℝ≥0 := fun _ => Real.toNNReal (1-t)
  let C : ℕ → ℝ≥0 := fun _ => ⟨c,hc0⟩
  have hH : (time H 1:ℝ)=1-t := by simp only [time_succ,time_zero,zero_add,H,Real.coe_toNNReal _ (sub_nonneg.mpr ht1.le)]
  have hb (n : ℕ) : |value W γ t x-logSemigroup c (Real.toNNReal (1-t)) abs x| ≤
      (2*Real.log 2)*(approxMesh n:ℝ) := by
    let M : ℝ := ((n+1:ℕ):ℝ)
    have hM : 0 < M := by dsimp [M];positivity
    have he (z : ℝ) : |softAbs M z-abs z| ≤ Real.log 2/M := by
      rw [abs_of_nonneg (softAbs_bounds hM z).1]
      exact (softAbs_bounds hM z).2
    have hv := cascadeV_value_error W γ t x ht0 ht1.le H C 1 hH
      (regularDatum_softAbs hM.ne') (softAbs_lipschitz hM.ne') he
    rw [plateau_grid_error_zero γ hc0 ht0 hat ht1 hc] at hv
    simp only [cascadeV,C,H,mul_zero,add_zero] at hv
    change |logSemigroup c (Real.toNNReal (1-t)) (softAbs M) x-value W γ t x| ≤ Real.log 2/M at hv
    have hv' : |value W γ t x-logSemigroup c (Real.toNNReal (1-t)) (softAbs M) x| ≤ Real.log 2/M := by
      simpa only [abs_sub_comm] using hv
    have hs := logSemigroup_terminal_stability (softAbs_lipschitz hM.ne') abs_lipschitz hc0 he (Real.toNNReal (1-t)) x
    have htri := abs_sub_le (value W γ t x) (logSemigroup c (Real.toNNReal (1-t)) (softAbs M) x)
      (logSemigroup c (Real.toNNReal (1-t)) abs x)
    have heM : Real.log 2/M+Real.log 2/M=(2*Real.log 2)*(approxMesh n:ℝ) := by
      simp only [M,approxMesh,NNReal.coe_inv,NNReal.coe_natCast]
      ring
    linarith
  have hz : Tendsto (fun n => (2*Real.log 2)*(approxMesh n:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul approxMesh_limit (a := 2*Real.log 2)
  have he := ge_of_tendsto hz (Eventually.of_forall hb)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))

lemma value_plateau_semigroup (W : BrownianSystem Ω) (γ : OrderParameter) {a c s T : ℝ}
    (hc0 : 0 ≤ c) (hs0 : 0 ≤ s) (has : a < s) (hsT : s ≤ T) (hT1 : T < 1)
    (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c) :
    value W γ s=varianceLogHeat c (T-s) (value W γ T) := by
  rw [value_on_terminal_plateau W γ hc0 hs0 has (hsT.trans_lt hT1) hc,
    value_on_terminal_plateau W γ hc0 (hs0.trans hsT) (has.trans_le hsT) hT1 hc,
    ← varianceLogHeat_add abs_lipschitz hc0 (sub_nonneg.mpr hsT) (sub_nonneg.mpr hT1.le)]
  congr 1
  ring

end ZeroTemperatureSK

end
end

end OAI
