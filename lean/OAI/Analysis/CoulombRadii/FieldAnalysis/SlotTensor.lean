import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.DeterminantWave

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

noncomputable def slotTensor {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) : ℂ :=
  ∏ j, if j = i then d (p j) (x j) else v (p j) (x j)

lemma slotTensor_factor {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) :
    slotTensor v d p i x = d (p i) (x i) * ∏ j ∈ Finset.univ.erase i, v (p j) (x j) := by
  unfold slotTensor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if j = i then d (p j) (x j) else v (p j) (x j)) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

lemma slotTensor_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    MemLp (slotTensor v d p i) 2 (Measure.pi fun _ : Fin n => μ) := by
  have H (j : Fin n) : MemLp (fun a => if j = i then d (p j) a else v (p j) a) 2 μ := by
    by_cases h : j = i
    · simpa only [ite_eq_left h] using hd (p j)
    · simpa only [ite_eq_right h] using hv (p j)
  exact scalarTensor_memLp (fun j a => if j = i then d (p j) a else v (p j) a) H id

lemma slotTensor_inner_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (∫ x, star (slotTensor v d p i x) * slotTensor v d q i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      (∫ a, star (d (p i) a) * d (q i) a ∂μ) *
        ∏ j ∈ Finset.univ.erase i, if p j = q j then (1:ℂ) else 0 := by
  simp only [slotTensor, star_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (f := fun j a =>
    star (if j = i then d (p j) a else v (p j) a) *
      (if j = i then d (q j) a else v (q j) a)) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∫ a,
    star (if j = i then d (p j) a else v (p j) a) *
      (if j = i then d (q j) a else v (q j) a) ∂μ) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1, ho]

noncomputable def slotDeterminant {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (i : Fin n) (x : Fin n → A) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) * slotTensor v d p i x

lemma slotDeterminant_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ) (i : Fin n) :
    MemLp (slotDeterminant v d i) 2 (Measure.pi fun _ : Fin n => μ) :=
  memLp_finsetSum _ (fun p _ => (slotTensor_memLp v d hv hd p i).const_mul _)

lemma slotDeterminant_bilinear {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (i : Fin n) (x : Fin n → A) :
    star (slotDeterminant v d i x) * slotDeterminant v d i x =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          (star (slotTensor v d p i x) * slotTensor v d q i x) := by
  simp only [slotDeterminant, star_sum, star_mul]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma slotDeterminant_inner_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (i : Fin n) :
    (∫ x, star (slotDeterminant v d i x) * slotDeterminant v d i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ((∫ a, star (d (p i) a) * d (q i) a ∂μ) *
            ∏ j ∈ Finset.univ.erase i, if p j = q j then (1:ℂ) else 0) := by
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x : Fin n → A => star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        (star (slotTensor v d p i x) * slotTensor v d q i x)) (Measure.pi fun _ => μ) :=
    ((slotTensor_memLp v d hv hd p i).star.integrable_mul
      (slotTensor_memLp v d hv hd q i)).const_mul _
  simp_rw [slotDeterminant_bilinear]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul, slotTensor_inner_integral v d ho]

lemma slotDeterminant_total_norm_sq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0) :
    (∑ i, ∫ x, ‖slotDeterminant v d i x‖^2 ∂(Measure.pi fun _ : Fin n => μ)) =
      (n.factorial : ℝ) * ∑ i, ∫ a, ‖d i a‖^2 ∂μ := by
  have hn (z : ℂ) : (↑(‖z‖^2) : ℂ) = star z * z := by
    rw [mul_comm, Complex.ofReal_pow]
    exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z).symm
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← integral_complex_ofReal, hn, slotDeterminant_inner_integral v d hv hd ho]
  calc
    _ = ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, (∫ a, star (d (p i) a) * d (q i) a ∂μ) *
            ∏ j ∈ Finset.univ.erase i, if p j = q j then (1:ℂ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
    _ = _ := slater_one_body_trace_algebra
      (fun a b => ∫ x, star (d a x) * d b x ∂μ)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
