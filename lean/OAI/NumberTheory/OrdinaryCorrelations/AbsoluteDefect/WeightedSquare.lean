import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryWeightedBinEnergy
open Finset

lemma weighted_square {ι : Type*} (I : Finset ι) (w c : ι → ℝ)
    (hw : ∀i∈I,0≤w i) :
    (∑i∈I,w i*c i)^2≤(∑i∈I,w i)*(∑i∈I,w i*(c i)^2) := by
  have hh := sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*c i)
  have h1 : (∑i∈I,Real.sqrt (w i)*(Real.sqrt (w i)*c i))=∑i∈I,w i*c i := by
    apply sum_congr rfl
    intro i hi
    rw [←mul_assoc,Real.mul_self_sqrt (hw i hi)]
  have h2 : (∑i∈I,Real.sqrt (w i)^2)=∑i∈I,w i := by
    apply sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have h3 : (∑i∈I,(Real.sqrt (w i)*c i)^2)=∑i∈I,w i*(c i)^2 := by
    apply sum_congr rfl
    intro i hi
    rw [mul_pow,Real.sq_sqrt (hw i hi)]
  rwa [h1,h2,h3] at hh

theorem energy {ι α : Type*} (I : Finset ι) (S : Finset α)
    (Q C : ι → α → ℂ) (w : ι → ℝ) (hw : ∀i∈I,0≤w i)
    (hQ : ∀i∈I,∀t∈S,‖Q i t‖≤w i) :
    (∑t∈S,‖∑i∈I,Q i t*C i t‖^2) ≤
      (∑i∈I,w i)*(∑i∈I,w i*(∑t∈S,‖C i t‖^2)) := by
  calc
    _ ≤ ∑t∈S,(∑i∈I,w i)*(∑i∈I,w i*‖C i t‖^2) := by
      apply sum_le_sum
      intro t ht
      apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
      have hm : (∑i∈I,‖Q i t*C i t‖)≤∑i∈I,w i*‖C i t‖ := by
        apply sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hQ i hi t ht) (norm_nonneg _)
      exact (pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) hm 2).trans
        (weighted_square I w (fun i => ‖C i t‖) hw)
    _ = _ := by rw [←mul_sum,sum_comm]; simp_rw [←mul_sum]

lemma energy_uniform {ι α : Type*} (I : Finset ι) (S : Finset α)
    (Q C : ι → α → ℂ) (w : ι → ℝ) (hw : ∀i∈I,0≤w i)
    (hQ : ∀i∈I,∀t∈S,‖Q i t‖≤w i) {η L : ℝ} (hη : 0≤η) (hL : 0≤L)
    (hmass : (∑i∈I,w i)≤L) (hC : ∀i∈I,(∑t∈S,‖C i t‖^2)≤η) :
    (∑t∈S,‖∑i∈I,Q i t*C i t‖^2) ≤ L^2*η := by
  apply (energy I S Q C w hw hQ).trans
  have hM : 0≤∑i∈I,w i := sum_nonneg hw
  calc
    _ ≤ (∑i∈I,w i)*(∑i∈I,w i*η) := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hC i hi) (hw i hi))
    _ = (∑i∈I,w i)^2*η := by rw [←sum_mul]; ring
    _ ≤ L^2*η := mul_le_mul_of_nonneg_right ((sq_le_sq₀ hM hL).mpr hmass) hη

end OrdinaryWeightedBinEnergy

end

end OAI
