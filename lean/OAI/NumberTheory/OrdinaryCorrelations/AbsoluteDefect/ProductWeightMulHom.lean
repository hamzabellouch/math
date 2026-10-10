import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BadFrequencies

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

namespace OrdinaryRestrictedCofactor
open Finset OrdinaryDirichletMeanSquare OrdinaryPrimeDirichletMoments
open OrdinaryDirichletFiberMoments SourcePrimeFactor

lemma productWeight_mul_hom (u : ℕ →* ℂ) (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) {k : ℕ}
    (z : (Fin k → P) × ℕ) :
    productWeight (fun n => u n * f n) χ P z =
      u (productLocation z) * productWeight f χ P z := by
  have hc (n : ℕ) : characterModulation (fun n => u n * f n) χ n =
      u n * characterModulation f χ n := by
    simp only [characterModulation, mul_assoc]
  have hp : tupleCoefficient
      (fun p => characterModulation (fun n => u n * f n) χ p / (p:ℂ)) z.1 =
      u (tupleProduct z.1) *
        tupleCoefficient (fun p => characterModulation f χ p / (p:ℂ)) z.1 := by
    simp only [tupleCoefficient, hc, mul_div_assoc, prod_mul_distrib,
      tupleProduct, map_prod]
  unfold productWeight
  rw [hp]
  simp only [OrdinaryCofactorDyadicBound.coefficient, hc, productLocation, map_mul]
  ring

lemma productCoefficient_mul_hom (u : ℕ →* ℂ) (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (k M n : ℕ) :
    productCoefficient (fun n => u n * f n) χ P k M n =
      u n * productCoefficient f χ P k M n := by
  classical
  unfold productCoefficient collect
  rw [mul_sum]
  apply sum_congr rfl
  intro z hz
  rw [productWeight_mul_hom, (mem_filter.mp hz).2]

lemma productLocation_pos {P : Finset ℕ} (hP : ∀p∈P,Nat.Prime p)
    {k M : ℕ} {z : (Fin k → P) × ℕ} (hz : z ∈ powersAndCofactors P k M) :
    0 < productLocation z := by
  have hm := (mem_Ioc.mp (mem_product.mp hz).2).1
  exact Nat.mul_pos (tupleProduct_pos hP z.1) (by omega)

theorem collectedEnergy_mul_unit_hom (u : ℕ →* ℂ)
    (hu : ∀n:ℕ,0<n → ‖u n‖=1) (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (k M : ℕ) :
    collectedEnergy (fun n => u n * f n) χ P k M = collectedEnergy f χ P k M := by
  classical
  unfold collectedEnergy
  apply sum_congr rfl
  intro n hn
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hn
  rw [productCoefficient_mul_hom, norm_mul, hu _ (productLocation_pos hP hz), one_mul]

def liouvilleHom : ℕ →* ℂ where
  toFun n := (ArithmeticFunction.liouville n:ℂ)
  map_one' := by simp [ArithmeticFunction.liouville_apply_one]
  map_mul' m n := by simp only [ArithmeticFunction.liouville_apply_mul, Int.cast_mul]

lemma liouvilleHom_norm {n : ℕ} (hn : 0<n) : ‖liouvilleHom n‖=1 := by
  change ‖(ArithmeticFunction.liouville n:ℂ)‖=1
  rw [ArithmeticFunction.liouville_apply hn.ne']
  simp

theorem collectedEnergy_liouville (q : ℕ) (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (k M : ℕ) :
    collectedEnergy (fun n => (ArithmeticFunction.liouville n:ℂ)) χ P k M =
      collectedEnergy (fun _ => 1) χ P k M := by
  have h := collectedEnergy_mul_unit_hom liouvilleHom (fun n hn => liouvilleHom_norm hn)
      (fun _ => 1) χ P hP k M
  simp only [mul_one] at h
  exact h

lemma liouville_prime {p : ℕ} (hp : Nat.Prime p) :
    (ArithmeticFunction.liouville p:ℂ)= -1 := by
  rw [ArithmeticFunction.liouville_apply hp.ne_zero,
    ArithmeticFunction.cardFactors_apply_prime hp]
  norm_num

lemma primeMellin_liouville {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (t : ℝ) :
    primeMellin (fun n => (ArithmeticFunction.liouville n:ℂ)) χ P t =
      -primeMellin (fun _ => 1) χ P t := by
  unfold primeMellin polynomial
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [characterModulation, liouville_prime (hP p hp)]
  ring

theorem badFrequencies_liouville {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p) (R : Finset ℝ) (V : ℝ) :
    badFrequencies (fun n => (ArithmeticFunction.liouville n:ℂ)) χ P R V =
      badFrequencies (fun _ => 1) χ P R V := by
  classical
  unfold badFrequencies
  apply filter_congr
  intro t ht
  rw [primeMellin_liouville χ P hP, norm_neg]

end OrdinaryRestrictedCofactor

end

end OAI
