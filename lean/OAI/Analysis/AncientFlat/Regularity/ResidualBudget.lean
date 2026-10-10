import OAI.Analysis.AncientFlat.Regularity.FreezingResidual

namespace OAI
noncomputable section
open scoped ContDiff
namespace ParabolicLocalization
open ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
def budgetFactor (A K : ℝ) : ℝ :=
  1+10*A+10*A*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖+
    10*A*(K+1)*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖+
    (20*A*K+10*A+150*K*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*A)
lemma budgetFactor_pos {A K : ℝ} (hA : 0≤A) (hK : 0≤K) : 0<budgetFactor (V := V) A K := by
  unfold budgetFactor; positivity
lemma residualBudget_le {A δ K F H N L : ℝ} (hA : 0≤A) (hδ : 0≤δ) (hδ1 : δ≤1)
    (hK : 0≤K) (hF : 0≤F) (hH : 0≤H) (hN : 0≤N) (hL : 0≤L) :
    residualBudget (V := V) A δ K F H N L≤budgetFactor (V := V) A K*(F+δ*H+N+L) := by
  let t := ‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖
  have ht : 0≤t := by dsimp [t]; positivity
  let P := budgetFactor (V := V) A K
  have h1 : 10*A≤P := by
    have hb : 0≤10*A*t := by positivity
    have hc : 0≤10*A*(K+1)*t := by positivity
    have hd : 0≤20*A*K+10*A+150*K*t*A := by positivity
    dsimp [P,budgetFactor,t] at *; linarith
  have h2 : 10*A*t≤P := by
    dsimp [P,budgetFactor,t]; nlinarith [mul_nonneg hA (show 0≤(K+1)*‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖ by positivity),mul_nonneg hA hK,mul_nonneg hK (show 0≤‖(traceFour : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ)‖*A by positivity)]
  have h3 : 10*A*(K+δ)*t≤P := by
    have hle : 10*A*(K+δ)*t≤10*A*(K+1)*t := by gcongr
    apply hle.trans
    dsimp [P,budgetFactor,t]
    nlinarith [mul_nonneg hA ht,mul_nonneg hA hK,mul_nonneg hK (show 0≤t*A by positivity)]
  have h4 : 20*A*K+10*A+150*K*t*A≤P := by
    dsimp [P,budgetFactor,t]
    nlinarith [mul_nonneg hA ht,mul_nonneg hA (show 0≤(K+1)*t by positivity)]
  calc
    _=10*A*F+10*A*t*(δ*H)+10*A*(K+δ)*t*N+(20*A*K+10*A+150*K*t*A)*L := by
      dsimp [residualBudget,t]; ring
    _≤P*F+P*(δ*H)+P*N+P*L := by
      gcongr
    _=_ := by ring
end ParabolicLocalization

end

end OAI
