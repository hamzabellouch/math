import OAI.Probability.ClassicalON.PositiveKernel

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def planarHamiltonian (left right : E → V) (b : E → ℝ) (θ : V → PlanarAngle) : ℝ :=
  ∑ e,b e*planarEnergy left right e θ

omit [Fintype V] in
theorem continuous_planarHamiltonian (left right : E → V) (b : E → ℝ) :
    Continuous (planarHamiltonian left right b) := by
  exact continuous_finsetSum _ (fun e _ => continuous_const.mul (continuous_planarEnergy _ _ e))

def planarMean (left right : E → V) (b : E → ℝ) (f : (V → PlanarAngle) → ℝ) : ℝ :=
  exponentialMean planarReference (planarHamiltonian left right b) f

omit [Fintype V] in
theorem planarHamiltonian_double (left right : E → V) (b : E → ℝ)
    (p : (V → PlanarAngle)×(V → PlanarAngle)) :
    planarHamiltonian left right b (torusDouble p).1+
      planarHamiltonian left right b (torusDouble p).2 =
      ∑ e,(2*b e)*(planarEnergy left right e p.1*planarEnergy left right e p.2) := by
  simp only [planarHamiltonian,← Finset.sum_add_distrib,← mul_add,
    planarEnergy_double_sum]
  apply Finset.sum_congr rfl; intro e _; ring

theorem planar_edge_covariance_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (e f : E) :
    planarMean left right b (planarEnergy left right e)*
      planarMean left right b (planarEnergy left right f) ≤
    planarMean left right b (fun θ => planarEnergy left right e θ*planarEnergy left right f θ) := by
  classical
  let T := planarEnergy left right
  let S := planarSine left right
  let H := planarHamiltonian left right b
  have hT : ∀ g,Continuous (T g) := continuous_planarEnergy _ _
  have hS : ∀ g,Continuous (S g) := continuous_planarSine _ _
  have hH : Continuous H := continuous_planarHamiltonian _ _ _
  let F : ((V → PlanarAngle)×(V → PlanarAngle)) → ℝ := fun p =>
    Real.exp (H p.1)*Real.exp (H p.2)*(T e p.1-T e p.2)*(T f p.1-T f p.2)
  have hF : Continuous F := by unfold F; fun_prop
  apply covariance_nonneg_of_doubled planarReference hH.rexp
    (fun θ => Real.exp_pos (H θ)) (hT e) (hT f)
  change 0≤∫ p,F p ∂(planarReference (V := V)).prod planarReference
  have hi : (∫ p,F (torusDouble p) ∂(planarReference (V := V)).prod planarReference)=
      ∫ p,F p ∂(planarReference (V := V)).prod planarReference := by
    have hm := integral_map (μ := (planarReference (V := V)).prod planarReference)
      (torusDouble_preserves (V := V)).measurable.aemeasurable
      hF.aestronglyMeasurable
    rw [(torusDouble_preserves (V := V)).map_eq] at hm
    exact hm.symm
  rw [← hi]
  have hp : (fun p => F (torusDouble p))=(fun p =>
      4*((S e p.1*S f p.1)*(S e p.2*S f p.2)*
        Real.exp (∑ g,(2*b g)*(T g p.1*T g p.2)))) := by
    funext p
    dsimp only [F,H,T,S]
    rw [← Real.exp_add,planarHamiltonian_double,
      planarEnergy_double_sub,planarEnergy_double_sub]
    ring
  rw [hp,integral_const_mul]
  apply mul_nonneg (by norm_num)
  exact exp_gram_integral_nonneg planarReference ((hS e).mul (hS f)) hT
    (fun g => 2*b g) (fun g => mul_nonneg (by norm_num) (hb g))

end ClassicalON

end

end OAI
