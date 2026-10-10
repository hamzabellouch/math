import Mathlib
import OAI.Probability.SKGap.Terminal.GibbsExpectation

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace SKGapCutoff
open MeasureTheory

lemma continuous_energy {n : ℕ} (x : Spin n) :
    Continuous (fun J : Interaction n => energy J x) := by
  unfold energy
  fun_prop

lemma continuous_partition (n : ℕ) : Continuous (partition (n := n)) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ => (continuous_energy x).rexp)

lemma continuous_gibbs {n : ℕ} (x : Spin n) :
    Continuous (fun J : Interaction n => gibbs J x) := by
  exact (continuous_energy x).rexp.div (continuous_partition n)
    (fun J => ne_of_gt (partition_pos J))

lemma continuous_field {n : ℕ} (x : Spin n) (i : Fin n) :
    Continuous (fun J : Interaction n => field J x i) := by
  unfold field
  fun_prop

lemma continuous_mean {n : ℕ} (x : Spin n) (i : Fin n) :
    Continuous (fun J : Interaction n => mean J x i) := by
  simp only [mean, Real.tanh_eq_sinh_div_cosh]
  exact (Real.continuous_sinh.comp (continuous_field x i)).div
    (Real.continuous_cosh.comp (continuous_field x i))
    (fun J => ne_of_gt (Real.cosh_pos (field J x i)))

lemma continuous_siteVariance {n : ℕ} (x : Spin n) (i : Fin n) :
    Continuous (fun J : Interaction n => siteVariance J x i) := by
  exact continuous_const.sub ((continuous_mean x i).pow 2)

lemma continuous_gibbsExpectation {n : ℕ} (f : Interaction n → Observables n)
    (hf : ∀ x, Continuous (fun J => f J x)) :
    Continuous (fun J => gibbsExpectation J (f J)) := by
  unfold gibbsExpectation
  exact continuous_finsetSum _ (fun x _ => (continuous_gibbs x).mul (hf x))

lemma continuous_gibbsVariance {n : ℕ} (f : Observables n) :
    Continuous (fun J : Interaction n => gibbsVariance J f) := by
  apply continuous_gibbsExpectation
  intro x
  exact (continuous_const.sub
    (continuous_gibbsExpectation (fun _ => f) (fun _ => continuous_const))).pow 2

lemma continuous_dirichlet {n : ℕ} (f g : Observables n) :
    Continuous (fun J : Interaction n => dirichlet J f g) := by
  apply continuous_gibbsExpectation
  intro x
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_siteVariance x i).mul continuous_const).mul continuous_const)

lemma isClosed_hasGap {n : ℕ} (γ : ℝ) :
    IsClosed {J : Interaction n | HasGap J γ} := by
  simp only [HasGap, Set.ofPred_forall]
  exact isClosed_iInter fun f => isClosed_le
    (continuous_const.mul (continuous_gibbsVariance f)) (continuous_dirichlet f f)

lemma continuous_sampledInteraction (n : ℕ) :
    Continuous (sampledInteraction (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : i = j
  · simp only [sampledInteraction, h, ite_true]
    exact continuous_const
  · simp only [sampledInteraction, h, ite_false]
    exact continuous_apply _

lemma measurableSet_sampledGap (n : ℕ) (γ : ℝ) :
    MeasurableSet {g : GaussianCoordinates n | HasGap (sampledInteraction g) γ} :=
  ((isClosed_hasGap γ).preimage (continuous_sampledInteraction n)).measurableSet

end SKGapCutoff

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

end

end OAI
