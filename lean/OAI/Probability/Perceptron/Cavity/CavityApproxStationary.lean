import Mathlib
import OAI.Probability.Perceptron.Variational.CoupledDual

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma finiteSphericalDual_approx_stationary {k : ℕ} (w h g : Fin (k+1)→ℝ)
    (q : Fin (k+1)→Time) (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1)
    (hh : Monotone h) (hh0 : 0≤h 0) (hg : Monotone g) (hg0 : 0≤g 0)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ)<1)
    (hs : ∀ i,2*g i=weightedStepA w (fun j=>(q j:ℝ)) (q i))
    {δ : ℝ} (_hδ : 0≤δ) (hd : ∀ i,|h i-g i|≤δ) :
    (entropy (weightedStepTrial w q (fun i=>(hw i).le) hw1)).toReal-
      (∑ i,w i*h i*(q i:ℝ))-2*δ ≤
      sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1) := by
  have hsum : (∑ i,w i*|h i-g i|)≤δ := by
    calc
      _≤∑ i,w i*δ:=Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (hd i) (hw i).le
      _=δ:=by rw [←Finset.sum_mul,hw1,one_mul]
  have hD:=finiteSphericalDual_abs_sub_le w h g hw hw1 hh hh0 hg hg0
  rw [finiteSphericalDual_eq_stationary w g q (fun i=>(hw i).le) hw1 hq hq1 hs] at hD
  unfold finiteSphericalDualObjective at hD
  have hterm : (∑ i,w i*g i*(q i:ℝ))-(∑ i,w i*h i*(q i:ℝ))≤δ := by
    calc
      _=∑ i,w i*((g i-h i)*(q i:ℝ)):=by rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
      _≤∑ i,w i*|h i-g i|:=by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i).le
        calc
          (g i-h i)*(q i:ℝ)≤|g i-h i| *(q i:ℝ):=mul_le_mul_of_nonneg_right (le_abs_self _) (q i).prop.1
          _≤|g i-h i| *1:=mul_le_mul_of_nonneg_left (q i).prop.2 (abs_nonneg _)
          _=|h i-g i|:=by rw [mul_one,abs_sub_comm]
      _≤δ:=hsum
  linarith [(abs_le.mp (hD.trans hsum)).1]


lemma terminalVariational_le_trial (P : Measure BrownianPath) [IsProbabilityMeasure P]
    {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (m : Trial) (hm : entropy m≠⊤) :
    (terminalVariational P α f).toReal ≤ α*controlValue P f m+(entropy m).toReal := by
  apply EReal.coe_le_coe_iff.mp
  rw [terminalVariational_coe_toReal P α hα f,EReal.coe_add,
    EReal.coe_ennreal_toReal hm]
  exact iInf_le _ m

lemma finiteCavity_trial_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    {α : ℝ} (hα : 0≤α) (f : ℝ→ᵇℝ) (n d : ℕ) {k : ℕ}
    (w h g : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1)
    (hh : Monotone h) (hh0 : 0≤h 0) (hg : Monotone g) (hg0 : 0≤g 0)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ)<1)
    (hs : ∀ i,2*g i=weightedStepA w (fun j=>(q j:ℝ)) (q i))
    {δ ε a : ℝ} (hδ : 0≤δ) (hd : ∀ i,|h i-g i|≤δ)
    (hdim : |finiteSphericalFieldValue n k w h-
      sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε)
    (hdα : |(d:ℝ)-(n+1:ℕ)*α|≤1) :
    (n+1:ℕ)*(a/2+(terminalVariational P α f).toReal-
      (∑ i,w i*h i*(q i:ℝ))-2*δ-ε)-‖f‖ ≤
    (n+1:ℕ)*(a/2+finiteSphericalFieldValue n k w h)+
      d*controlValue P f (weightedStepTrial w q (fun i=>(hw i).le) hw1) := by
  let m:=weightedStepTrial w q (fun i=>(hw i).le) hw1
  have hm : entropy m≠⊤ := by
    rw [entropy_weightedStepTrial w q (fun i=>(hw i).le) hw1 (q (Fin.last k))
      (q (Fin.last k)).prop.1 hq1 (fun i=>hq (Fin.le_last i))]
    exact ENNReal.ofReal_ne_top
  have hv:=terminalVariational_le_trial P hα f m hm
  have hstat:=finiteSphericalDual_approx_stationary w h g q hw hw1 hh hh0 hg hg0 hq hq1 hs hδ hd
  have hcv : |controlValue P f m|≤‖f‖ :=
    abs_le.mpr ⟨neg_norm_le_controlValue P f m,controlValue_le_norm P f m⟩
  have he : |((d:ℝ)-(n+1:ℕ)*α)*controlValue P f m|≤‖f‖ := by
    rw [abs_mul]
    exact (mul_le_mul hdα hcv (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hL : (0:ℝ)≤(n+1:ℕ):=by positivity
  have hlo := mul_le_mul_of_nonneg_left (le_of_lt (abs_lt.mp hdim).1) hL
  have hslo := mul_le_mul_of_nonneg_left hstat hL
  have hvlo := mul_le_mul_of_nonneg_left hv hL
  dsimp only [m] at hvlo he
  nlinarith [(abs_le.mp he).1]
end SphericalPerceptronFreeEnergy

end

end OAI
