import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FinEquivApply

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
open ArithmeticFunction
open MeasureTheory Finset
open Classical

namespace OrdinaryCorrelations.FiniteResidues

lemma mass_nonneg (d a N : ℕ) [NeZero d] (z : ZMod d) : 0 ≤ mass d a N z := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma sum_mass_test (d a N : ℕ) [NeZero d] (f : ZMod d → ℝ) :
    (∑ z, mass d a N z * f z) =
      (∑ i ∈ Finset.range N, f ((a+i : ℕ) : ZMod d)) / N := by
  unfold mass
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp_rw [count, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

lemma sum_mass (d a N : ℕ) [NeZero d] (hN : 0 < N) :
    (∑ z, mass d a N z) = 1 := by
  have h := sum_mass_test d a N (fun _ => 1)
  simpa [ne_of_gt hN] using h

def cubeMean (d a N : ℕ) [NeZero d] (F : ZMod d → ZMod d → ZMod d → ℝ) : ℝ :=
  (N:ℝ)⁻¹^3 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
    F ((a+i : ℕ) : ZMod d) ((a+j : ℕ) : ZMod d) ((a+k : ℕ) : ZMod d)

def uniformCubeMean (d : ℕ) [NeZero d] (F : ZMod d → ZMod d → ZMod d → ℝ) : ℝ :=
  (d:ℝ)⁻¹^3 * ∑ x, ∑ y, ∑ z, F x y z

lemma cubeMean_eq (d a N : ℕ) [NeZero d] (F : ZMod d → ZMod d → ZMod d → ℝ) :
    cubeMean d a N F = ∑ x, ∑ y, ∑ z,
      mass d a N x * mass d a N y * mass d a N z * F x y z := by
  have he : (∑ x, ∑ y, ∑ z,
      mass d a N x * mass d a N y * mass d a N z * F x y z) =
      ∑ x, mass d a N x * ∑ y, mass d a N y * ∑ z, mass d a N z * F x y z := by
    simp_rw [Finset.mul_sum]
    congr 1; ext x
    congr 1; ext y
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  rw [sum_mass_test]
  simp_rw [sum_mass_test]
  unfold cubeMean
  simp_rw [div_eq_mul_inv,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma product_mass_discrepancy (d a N : ℕ) [NeZero d] (hN : 0 < N) :
    (∑ x : ZMod d, ∑ y : ZMod d, ∑ z : ZMod d,
      |mass d a N x * mass d a N y * mass d a N z - (d:ℝ)⁻¹^3|) ≤
       3 * (d:ℝ) / N := by
  let p := mass d a N
  let u : ℝ := (d:ℝ)⁻¹
  have hp (x : ZMod d) : 0 ≤ p x := mass_nonneg d a N x
  have hu : 0 ≤ u := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hs : ∑ x, p x = 1 := sum_mass d a N hN
  have hd : (d:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have huone : (d:ℝ)*u = 1 := mul_inv_cancel₀ hd
  have hb (x y z : ZMod d) :
      |p x*p y*p z-u^3| ≤ |p x-u| * p y*p z + u * |p y-u| * p z + u*u * |p z-u| := by
    have he : p x*p y*p z-u^3 =
        (p x-u)*p y*p z + u*(p y-u)*p z + u*u*(p z-u) := by ring
    rw [he]
    calc
      _ ≤ |(p x-u)*p y*p z + u*(p y-u)*p z| + |u*u*(p z-u)| := abs_add_le _ _
      _ ≤ (|(p x-u)*p y*p z| + |u*(p y-u)*p z|) + |u*u*(p z-u)| :=
        _root_.add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by simp only [abs_mul,abs_of_nonneg (hp y),abs_of_nonneg (hp z),abs_of_nonneg hu]
  have he : (∑ x : ZMod d, ∑ y : ZMod d, ∑ z : ZMod d,
      (|p x-u| * p y*p z + u * |p y-u| * p z + u*u * |p z-u|)) =
      3 * ∑ x : ZMod d, |p x-u| := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hs, mul_one,
      Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    have hu2 : (d:ℝ)*((d:ℝ)*(u*u)) = 1 := by
      calc
        _ = ((d:ℝ)*u)*((d:ℝ)*u) := by ring
        _ = _ := by rw [huone]; norm_num
    calc
      _ = (1 + (d:ℝ)*u + (d:ℝ)*((d:ℝ)*(u*u))) * ∑ x : ZMod d, |p x-u| := by ring
      _ = _ := by rw [huone,hu2]; ring
  have htv : (∑ x : ZMod d, |p x-u|) ≤ (d:ℝ) / N := by
    calc
      _ ≤ ∑ x : ZMod d, (N:ℝ)⁻¹ := Finset.sum_le_sum (fun x _ => mass_discrepancy d a N hN x)
      _ = _ := by simp [div_eq_mul_inv]
  calc
    _ ≤ _ := Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ =>
        Finset.sum_le_sum (fun z _ => hb x y z)))
    _ = _ := he
    _ ≤ 3 * ((d:ℝ) / N) := mul_le_mul_of_nonneg_left htv (by norm_num)
    _ = _ := by ring

theorem cube_boundary (d a N : ℕ) [NeZero d] (hN : 0 < N)
    (F : ZMod d → ZMod d → ZMod d → ℝ) (hF : ∀ x y z, |F x y z| ≤ 1) :
    |cubeMean d a N F - uniformCubeMean d F| ≤ 3*(d:ℝ)/N := by
  rw [cubeMean_eq]
  have he : (∑ x, ∑ y, ∑ z, mass d a N x * mass d a N y * mass d a N z * F x y z) -
      uniformCubeMean d F = ∑ x, ∑ y, ∑ z,
      (mass d a N x * mass d a N y * mass d a N z - (d:ℝ)⁻¹^3)*F x y z := by
    unfold uniformCubeMean
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib,sub_mul]
  rw [he]
  calc
    _ ≤ ∑ x, |∑ y, ∑ z, (mass d a N x*mass d a N y*mass d a N z-(d:ℝ)⁻¹^3)*F x y z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, ∑ z, |(mass d a N x*mass d a N y*mass d a N z-(d:ℝ)⁻¹^3)*F x y z| := by
      apply Finset.sum_le_sum
      intro x _
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ =>
        Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ x, ∑ y, ∑ z, |mass d a N x*mass d a N y*mass d a N z-(d:ℝ)⁻¹^3| := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF x y z)
    _ ≤ _ := product_mass_discrepancy d a N hN

end OrdinaryCorrelations.FiniteResidues

end

end OAI
