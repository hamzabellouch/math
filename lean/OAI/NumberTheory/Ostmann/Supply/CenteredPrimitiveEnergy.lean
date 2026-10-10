import OAI.NumberTheory.Ostmann.Supply.CRTPrimitiveEnergy
import OAI.NumberTheory.Ostmann.Supply.CompletionWeights
import OAI.NumberTheory.Ostmann.Supply.ResidueTensor

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Finset
open scoped BigOperators ComplexConjugate

def supportRatio (S : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) : ℝ :=
  (p : ℝ) / (S p).card - 1

def centeredInner (S : ∀ p : ℕ, Finset (ZMod p)) (p a b : ℕ) : ℂ :=
  if hp : p = 0 then 0 else
    letI : NeZero p := ⟨hp⟩
    inner ℂ (centeredProjection (S p) (EuclideanSpace.single (a : ZMod p) 1))
      (centeredProjection (S p) (EuclideanSpace.single (b : ZMod p) 1))

@[simp] theorem centeredInner_eq (S : ∀ p : ℕ, Finset (ZMod p)) (p a b : ℕ)
    [NeZero p] : centeredInner S p a b =
      inner ℂ (centeredProjection (S p) (EuclideanSpace.single (a : ZMod p) 1))
        (centeredProjection (S p) (EuclideanSpace.single (b : ZMod p) 1)) := by
  simp [centeredInner, NeZero.ne p]

def centeredEnergy (A : Finset ℕ) (S : ∀ p : ℕ, Finset (ZMod p)) (t : ℕ) : ℝ :=
  letI : ∀ p : t.primeFactors, NeZero (p : ℕ) :=
    fun p => ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  tensorEnergy A (residueVectors (fun p : t.primeFactors => (p : ℕ)) (fun p => S p))

theorem centeredEnergy_nonneg (A : Finset ℕ) (S : ∀ p : ℕ, Finset (ZMod p)) (t : ℕ) :
    0 ≤ centeredEnergy A S t := by
  let : ∀ p : t.primeFactors, NeZero (p : ℕ) :=
    fun p => ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  exact tensorEnergy_nonneg _ _

theorem centeredEnergy_eq_gram (A : Finset ℕ) (S : ∀ p : ℕ, Finset (ZMod p)) (t : ℕ) :
    (centeredEnergy A S t : ℂ) = (A.card : ℂ)⁻¹^2 *
    ∑ a ∈ A, ∑ b ∈ A, ∏ p ∈ t.primeFactors, centeredInner S p a b := by
  let : ∀ p : t.primeFactors, NeZero (p : ℕ) :=
    fun p => ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  rw [centeredEnergy, tensorEnergy_eq_gram]
  congr 1
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [← prod_coe_sort t.primeFactors]
  apply prod_congr rfl
  intro p hp
  simp only [residueVectors, centeredInner_eq]

theorem centeredEnergy_one (A : Finset ℕ) (hA : A.Nonempty)
    (S : ∀ p : ℕ, Finset (ZMod p)) : centeredEnergy A S 1 = 1 := by
  apply Complex.ofReal_injective
  rw [centeredEnergy_eq_gram]
  have hn : (A.card : ℂ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr hA
  simp only [Nat.primeFactors_one, prod_empty, sum_const, nsmul_eq_mul, mul_one,
    Complex.ofReal_one]
  field_simp

def primitiveEnergy (A : Finset ℕ) (q : ℕ) : ℝ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖normalizedExpSum A (((u : ZMod q).val : ℝ) / q)‖^2

@[simp] theorem primitiveEnergy_eq (A : Finset ℕ) (q : ℕ) [NeZero q] :
    primitiveEnergy A q =
      ∑ u : (ZMod q)ˣ, ‖normalizedExpSum A (((u : ZMod q).val : ℝ) / q)‖^2 := by
  simp [primitiveEnergy, NeZero.ne q]

theorem primitiveEnergy_nonneg (A : Finset ℕ) (q : ℕ) : 0 ≤ primitiveEnergy A q := by
  unfold primitiveEnergy
  split
  · exact le_rfl
  · exact sum_nonneg (fun u hu => sq_nonneg _)

theorem centeredKernel_powerset (A : Finset ℕ) (S : ∀ p : ℕ, Finset (ZMod p))
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ a ∈ A, ∑ b ∈ A, ∏ p ∈ s,
      ((p : ℂ) * centeredInner S p a b + supportRatio S p)) / (A.card : ℂ)^2 =
    ∑ t ∈ s.powerset, ((∏ p ∈ t, p : ℕ) : ℂ) *
      centeredEnergy A S (∏ p ∈ t, p) * ∏ p ∈ s \ t, (supportRatio S p : ℂ) := by
  simp_rw [prod_add]
  simp_rw [sum_comm (s := A) (t := s.powerset)]
  rw [sum_div]
  apply sum_congr rfl
  intro t ht
  rw [centeredEnergy_eq_gram, Nat.primeFactors_prod (fun p hp => hs p (mem_powerset.mp ht hp))]
  simp only [prod_mul_distrib, Nat.cast_prod]
  rw [sum_div]
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro a ha
  rw [sum_div]
  apply sum_congr rfl
  intro b hb
  rw [div_eq_mul_inv, ← inv_pow]
  ring

theorem sum_divisors_eq_powerset {R : Type*} [AddCommMonoid R] {q : ℕ}
    (hq : Squarefree q) (f : ℕ → R) :
    ∑ t ∈ q.divisors, f t = ∑ s ∈ q.primeFactors.powerset, f (∏ p ∈ s, p) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hq,
    Nat.sum_divisors_filter_squarefree hq.ne_zero, Nat.factors_eq]
  simp only [List.toFinset_coe, ← Nat.toFinset_factors, Finset.prod_val, Function.id_def]

theorem primitiveEnergy_centered_expansion (A : Finset ℕ)
    (S : ∀ p : ℕ, Finset (ZMod p)) {q : ℕ} (hq : Squarefree q)
    (hS : ∀ a ∈ A, ∀ p ∈ q.primeFactors, (a : ZMod p) ∈ S p) :
    primitiveEnergy A q = ∑ t ∈ q.divisors,
      (t : ℝ) * centeredEnergy A S t *
        CompletionCounting.primeProduct (supportRatio S) (q / t) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  apply Complex.ofReal_injective
  rw [primitiveEnergy_eq, normalizedExpSum_primitive_energy_complex hq A]
  have hkernel : (∑ a ∈ A, ∑ b ∈ A, ∏ p ∈ q.primeFactors,
      ((p : ℂ) * (if (a : ZMod p) = (b : ZMod p) then 1 else 0) - 1)) =
      ∑ a ∈ A, ∑ b ∈ A, ∏ p ∈ q.primeFactors,
        ((p : ℂ) * centeredInner S p a b + supportRatio S p) := by
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    apply prod_congr rfl
    intro p hp
    let : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    simpa only [centeredInner_eq, supportRatio, complementRatio] using
      primeKernel_centered (S p) _ _ (hS a ha p hp) (hS b hb p hp)
  rw [hkernel, centeredKernel_powerset A S q.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp), sum_divisors_eq_powerset hq]
  push_cast
  apply sum_congr rfl
  intro t ht
  rw [CompletionCounting.primeProduct,
    ← Nat.prod_primeFactors_sdiff_of_squarefree hq (mem_powerset.mp ht),
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1)]
  push_cast
  rfl

end Ostmann.Supply

end

end OAI
