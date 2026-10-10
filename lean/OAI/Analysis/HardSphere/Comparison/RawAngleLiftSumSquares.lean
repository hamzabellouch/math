import Mathlib
import OAI.Analysis.HardSphere.Geometry.RawAngleLift

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open PeriodicCutoff

lemma rawAngleLift_sum_squares (n : ℕ) (L : Length) (r : ℝ) (i : Fin n)
    (R : LiftedConfiguration (n+1)) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) R
      (Pi.single p.1 (Pi.single p.2 1)))^2)=
      2*∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
  simp only [rawAngleLift_fderiv_coord]
  rw [Fintype.sum_prod_type,Fin.sum_univ_succ]
  simp only [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i),ite_true,ite_false,sub_zero,one_mul,
    Fin.succ_inj,zero_sub,neg_mul,neg_sq]
  have he : (∑ k : Fin n, ∑ j : Fin 3,
      ((if k=i then (1:ℝ) else 0)*anglePartial L.val r (R 0-R i.succ) j)^2)=
      ∑ j : Fin 3, anglePartial L.val r (R 0-R i.succ) j^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [he]
  ring

lemma pairQ_representative (n : ℕ) (L : Length) (i : Fin n) (X : Configuration (n+1) L) :
    pairQ L.val (X 0) (X i.succ)=qLift L.val
      (representative (n+1) L X 0-representative (n+1) L X i.succ) := by
  calc
    _ = pairQ L.val (project (n+1) L (representative (n+1) L X) 0)
      (project (n+1) L (representative (n+1) L X) i.succ) := by rw [project_representative]
    _ = _ := pairQ_coe L.val _ _

lemma rawAngleLift_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M)
    (i : Fin n) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
      (Pi.single p.1 (Pi.single p.2 1)))^2)≤
      (6*Real.pi^2*M^2/r^2)*(box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  rw [rawAngleLift_sum_squares]
  by_cases hx : X 0∈box L.val (Real.pi*r) (X i.succ)
  · rw [Set.indicator_of_mem hx,mul_one]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _ ↦ anglePartial_sq_le L.val hr hM hb
        (representative (n+1) L X 0-representative (n+1) L X i.succ) j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    calc
      _ ≤ 2*((3:ℝ)*(Real.pi^2*M^2/r^2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx,mul_zero]
    have hq := not_mem_box_pairQ L.val hr hx
    rw [pairQ_representative] at hq
    have hz : qLift L.val (representative (n+1) L X 0-representative (n+1) L X i.succ)∉Icc (2*r^2) (4*r^2) :=
      fun hs ↦ (not_lt.mpr hs.2) hq
    simp [anglePartial_eq_zero L.val hr hz]

lemma rawCutoff_gradient_le (n : ℕ) (L : Length) {r M : ℝ} (hr : 0<r) (hM : 0≤M)
    (hb : ∀ t : ℝ, |deriv Real.smoothTransition t|≤M) (X : Configuration (n+1) L) :
    (∑ p : Direction (n+1), ‖coordDerivative (n+1) L (rawCutoff n L r).toFun p X‖^2)≤
      (6*Real.pi^2*M^2/r^2)*∑ i : Fin n,
        (box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) := by
  calc
    _ ≤ ∑ p : Direction (n+1), ∑ i : Fin n,
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 :=
      Finset.sum_le_sum fun p _ ↦ rawCutoff_derivative_sq_le n L r X p
    _ = ∑ i : Fin n, ∑ p : Direction (n+1),
        (fderiv ℝ (rawAngleLift n L r i) (representative (n+1) L X)
          (Pi.single p.1 (Pi.single p.2 1)))^2 := by rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin n, (6*Real.pi^2*M^2/r^2)*
        (box L.val (Real.pi*r) (X i.succ)).indicator (fun _ ↦ (1:ℝ)) (X 0) :=
      Finset.sum_le_sum fun i _ ↦ rawAngleLift_gradient_le n L hr hM hb i X
    _ = _ := (Finset.mul_sum ..).symm

end HardSphere

end

end OAI
