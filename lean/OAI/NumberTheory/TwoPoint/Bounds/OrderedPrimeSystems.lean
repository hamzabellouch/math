import OAI.NumberTheory.TwoPoint.Bounds.OrderedElimination
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalLaw

namespace OAI

/-! A finite ordered family packages the precise output of witness selection. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- The index order records elimination order; it is unrelated to the
names or numerical values of the ambient prime labels. -/
structure OrderedPrimeSystem (ι : Type*) [DecidableEq ι] where
  Index : Type
  [indexFintype : Fintype Index]
  [indexOrder : LinearOrder Index]
  Term : Index → Type
  [termFintype : ∀ i, Fintype (Term i)]
  relation : (i : Index) → Term i → PrimeMonomial ι
  selected : Index → ι
  control : Index → ι
  control_ne : ∀ i, control i ≠ selected i
  triangular : ∀ i j, i < j →
    selected j ∉ primeRelationSupport (relation i) ∧ control i ≠ selected j

attribute [instance] OrderedPrimeSystem.indexFintype OrderedPrimeSystem.indexOrder
  OrderedPrimeSystem.termFintype

namespace OrderedPrimeSystem

variable {ι : Type*} [DecidableEq ι]

def size (S : OrderedPrimeSystem ι) : ℕ := Fintype.card S.Index

def Holds (S : OrderedPrimeSystem ι) (x : ι → ℤ) : Prop :=
  ∀ i, primeRelationEvent (S.relation i) (S.selected i) (S.control i) x

/-- Each selected interval or comparison earns its own factor; every
unselected prime variable is averaged with its original product law. -/
theorem probability_bound [Fintype ι] {A : Type*} [Fintype A] [Nonempty A]
    (S : OrderedPrimeSystem ι) (μ : ι → FiniteLaw A) (value : A → ℕ)
    (hinj : Function.Injective value) (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hprime : ∀ a, (value a).Prime) (hlo : ∀ a, H ≤ value a)
    (hhi : ∀ a, value a ≤ N) (hweight : ∀ i a, (μ i).weight a ≤ (value a : ℝ)⁻¹) :
    (FiniteLaw.independent μ).probability (fun x => S.Holds (integerPrimeAssignment value x)) ≤
      ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ S.size := by
  simpa only [Holds, Finset.mem_univ, forall_true_left, card_univ, size] using
    FiniteLaw.ordered_prime_relation_probability S.Term μ value hinj H N hH hN hprime
      hlo hhi hweight S.relation S.selected S.control univ
      (fun i _ => S.control_ne i) (fun i _ j _ hij => S.triangular i j hij)

/-- The actual reciprocal sum for a fixed recorded system. Keeping the
nonzero coefficient tests in `Holds` makes every elimination valid after
resampling, including samples with coincident numerical primes. -/
theorem reciprocal_sum_bound [Fintype ι] (S : OrderedPrimeSystem ι)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hV : 1 ≤ primeHarmonicMass P)
    (H N : ℕ) (hH : 0 < H) (hN : 1 ≤ N)
    (hlo : ∀ p ∈ P, H ≤ p) (hhi : ∀ p ∈ P, p ≤ N) :
    (∑ x : ι → P, if S.Holds (integerPrimeAssignment Subtype.val x)
      then ∏ z, ((x z).val : ℝ)⁻¹ else 0) ≤
      primeHarmonicMass P ^ Fintype.card ι *
        ((H : ℝ)⁻¹ + (1 + Real.log N) / H) ^ S.size := by
  classical
  have hVp : 0 < primeHarmonicMass P := lt_of_lt_of_le zero_lt_one hV
  have hPnonempty : Nonempty P := by
    have hPn : P.Nonempty := by
      by_contra hn
      have hpempty : P = ∅ := not_nonempty_iff_eq_empty.mp hn
      have hz : primeHarmonicMass P = 0 := by
        subst P
        simp [primeHarmonicMass]
      linarith
    obtain ⟨p, hp⟩ := hPn
    exact ⟨⟨p, hp⟩⟩
  have : Nonempty P := hPnonempty
  apply primeReciprocalLaw_restore_bound P hVp _ _
  apply S.probability_bound (fun _ => primeReciprocalLaw P hVp) Subtype.val
    Subtype.val_injective H N hH hN (fun p => hP p.val p.property)
    (fun p => hlo p.val p.property) (fun p => hhi p.val p.property)
  intro i p
  change (p.val : ℝ)⁻¹ / primeHarmonicMass P ≤ (p.val : ℝ)⁻¹
  exact div_le_self (by positivity) hV

end OrderedPrimeSystem

end TwoPointCorrelations

end OAI
