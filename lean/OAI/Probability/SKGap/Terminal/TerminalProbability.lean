import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalDeterministic
import OAI.Probability.SKGap.Brownian.GibbsContinuity
import OAI.Probability.SKGap.Localization.RareCoordinate
import OAI.Probability.SKGap.Posterior.GaussianChannel

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

def observationField (T : ℝ) (x : Spin n) (z : Fin n→ℝ) : Fin n→ℝ :=
  fun i=>T*spinValue (x i)+sqrt T*z i

lemma spinValue_sign (b : Bool) : spinValue b=1 ∨ spinValue b= -1 := by
  cases b <;> simp

lemma rareCount_field (T : ℝ) (x : Spin n) (z : Fin n→ℝ) :
    rareCount (fun i=>{u : ℝ | |T*spinValue (x i)+sqrt T*u| < T/2}) z=
      ((Finset.univ.filter (fun i=>|observationField T x z i| < T/2)).card:ℝ) := by
  classical
  simp only [rareCount,observationField,Set.mem_ofPred_eq]
  simp only [Finset.sum_boole]
  rfl

lemma observation_smallField_tail {T α : ℝ} (hT : 0 < T)
    (hp : exp (-T/8)*(exp 1-1) ≤ α/4) (x : Spin n) :
    (channelReference n).real {z | α*(n:ℝ)/2 <
      ((Finset.univ.filter (fun i=>|observationField T x z i| < T/2)).card:ℝ)} ≤
        exp (-α*(n:ℝ)/4) := by
  classical
  have hh := rareCount_tail (fun _ : Fin n=>gaussianReal 0 1)
    (fun i=>{u : ℝ | |T*spinValue (x i)+sqrt T*u| < T/2})
    (fun _=>isOpen_lt (by fun_prop) continuous_const |>.measurableSet)
    (a:=α*(n:ℝ)/2) (fun i=>gaussian_observation_small hT (spinValue_sign (x i)))
  simp only [rareCount_field,Fintype.card_fin] at hh
  apply hh.trans
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith only [hm]

theorem terminal_probability_fixedSpin (g : Disorder n) {M T α ε R : ℝ}
    (hM : 0 ≤ M) (hT : 0 < T) (hε : 0 ≤ ε)
    (hJ : ‖Matrix.of (coupling g)‖ ≤ M)
    (hU : ‖terminalU g‖ ≤ M) (hQ : ‖terminalQ g‖ ≤ M)
    (hc : ∀ i j,|tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i,∑ j,tanh (coupling g i j)^4 ≤ R)
    (hsparse : ∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
      ∀ w : EuclideanSpace ℝ (Fin n),(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalU g) w⟫| ≤ ε*‖w‖^2 ∧
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalQ g) w⟫| ≤ ε*‖w‖^2)
    (hsmall : M^2 ≤ (T/4)^2*α/2)
    (hnum : 800000*R+400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2)) ≤ 1/2)
    (hp : exp (-T/8)*(exp 1-1) ≤ α/4) (x : Spin n) :
    (channelReference n).real {z | ¬∀ f : Spin n→ℝ,
      variance g (observationField T x z) f ≤ 2*dirichlet g (observationField T x z) f} ≤
        exp (-α*(n:ℝ)/4) := by
  apply (measureReal_mono (μ:=channelReference n) ?_ (measure_ne_top _ _)).trans
    (observation_smallField_tail hT hp x)
  intro z hz
  by_contra hn
  change ¬α*(n:ℝ)/2 < ((Finset.univ.filter (fun i=>|observationField T x z i| < T/2)).card:ℝ) at hn
  have hb := le_of_not_gt hn
  apply hz
  apply terminal_deterministic g (observationField T x z) hM (by positivity : 0 < T/4) hε hJ hU hQ hc hR hsparse
    ?_ hsmall hnum
  simpa only [show 2*(T/4)=T/2 by ring] using hb

lemma terminal_bad_measurable (g : Disorder n) (T : ℝ) :
    MeasurableSet {p : Spin n × (Fin n→ℝ) | ¬∀ f : Spin n→ℝ,
      variance g (observationField T p.1 p.2) f ≤ 2*dirichlet g (observationField T p.1 p.2) f} := by
  apply ((terminal_goodSet_closed g 2).measurableSet.compl).preimage
  unfold observationField
  apply Measurable.of_eval
  intro i
  exact (measurable_const.mul ((measurable_of_finite (spinValue)).comp ((measurable_pi_apply i).comp measurable_fst))).add
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))

lemma terminal_probability_anyLaw (g : Disorder n) {T c : ℝ}
    (hh : ∀ x : Spin n,(channelReference n).real {z | ¬∀ f : Spin n→ℝ,
      variance g (observationField T x z) f ≤ 2*dirichlet g (observationField T x z) f} ≤ exp (-c*(n:ℝ)))
    (μ : Measure (Spin n)) [IsProbabilityMeasure μ] :
    (μ.prod (channelReference n)).real {p | ¬∀ f : Spin n→ℝ,
      variance g (observationField T p.1 p.2) f ≤ 2*dirichlet g (observationField T p.1 p.2) f} ≤ exp (-c*(n:ℝ)) := by
  have hb (x : Spin n) : channelReference n {z | ¬∀ f : Spin n→ℝ,
      variance g (observationField T x z) f ≤ 2*dirichlet g (observationField T x z) f} ≤ ENNReal.ofReal (exp (-c*(n:ℝ))) := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      (by simpa only [measureReal_def,ENNReal.toReal_ofReal (exp_pos _).le] using hh x)
  have he := Measure.prod_apply (μ:=μ) (ν:=channelReference n) (terminal_bad_measurable g T)
  have hh' : μ.prod (channelReference n) {p | ¬∀ f : Spin n→ℝ,
      variance g (observationField T p.1 p.2) f ≤ 2*dirichlet g (observationField T p.1 p.2) f} ≤ ENNReal.ofReal (exp (-c*(n:ℝ))) := by
    rw [he]
    calc
      _ ≤ ∫⁻ _x,ENNReal.ofReal (exp (-c*(n:ℝ))) ∂μ := lintegral_mono hb
      _ = _ := by simp
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh'
  simpa only [measureReal_def,ENNReal.toReal_ofReal (exp_pos _).le] using hr
end SKGap

end
end

end OAI
