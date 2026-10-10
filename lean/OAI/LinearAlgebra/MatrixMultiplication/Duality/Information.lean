import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels
import OAI.LinearAlgebra.MatrixMultiplication.Duality.EntropyHelpers

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation DualEntropyHelpers
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w

variable {A : Type u} [Fintype A] {X : Type w} [Fintype X]

def ConditionalIndependent {R L : Type*} [Fintype R] [Fintype L]
    (p : FiniteLaw A) (prior : A → R) (label : A → L) (x : A → X) : Prop :=
  ∀ r, 0 < (p.map prior).mass r → ∀ l xx,
    ((p.conditional prior r).map (fun a => (label a, x a))).mass (l, xx) =
      ((p.conditional prior r).map label).mass l *
        ((p.conditional prior r).map x).mass xx

def ConditionalMassFactorization {R L : Type*} [Fintype R] [Fintype L]
    (p : FiniteLaw A) (prior : A → R) (label : A → L) (x : A → X) : Prop :=
  ∀ r l xx,
    (p.map (fun a => (prior a, (label a, x a)))).mass (r, (l, xx)) *
        (p.map prior).mass r =
      (p.map (fun a => (prior a, label a))).mass (r, l) *
        (p.map (fun a => (prior a, x a))).mass (r, xx)

theorem conditionalIndependent_of_mass_factorization {R L : Type*}
    [Fintype R] [Fintype L] (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X)
    (factor : ConditionalMassFactorization p prior label x) :
    ConditionalIndependent p prior label x := by
  intro r hr l xx
  have h := factor r l xx
  rw [← p.map_mass_mul_conditional_map prior (fun a => (label a, x a)) r (l, xx),
    ← p.map_mass_mul_conditional_map prior label r l,
    ← p.map_mass_mul_conditional_map prior x r xx] at h
  apply mul_left_cancel₀ (mul_ne_zero hr.ne' hr.ne')
  calc
    ((p.map prior).mass r * (p.map prior).mass r) *
        ((p.conditional prior r).map (fun a => (label a, x a))).mass (l, xx) =
        ((p.map prior).mass r *
          ((p.conditional prior r).map (fun a => (label a, x a))).mass (l, xx)) *
            (p.map prior).mass r := by ring
    _ = ((p.map prior).mass r * ((p.conditional prior r).map label).mass l) *
        ((p.map prior).mass r * ((p.conditional prior r).map x).mass xx) := h
    _ = ((p.map prior).mass r * (p.map prior).mass r) *
        (((p.conditional prior r).map label).mass l *
          ((p.conditional prior r).map x).mass xx) := by ring

theorem mass_factorization_of_conditionalIndependent {R L : Type*}
    [Fintype R] [Fintype L] (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X)
    (independent : ConditionalIndependent p prior label x) :
    ConditionalMassFactorization p prior label x := by
  intro r l xx
  rw [← p.map_mass_mul_conditional_map prior (fun a => (label a, x a)) r (l, xx),
    ← p.map_mass_mul_conditional_map prior label r l,
    ← p.map_mass_mul_conditional_map prior x r xx]
  by_cases hr : (p.map prior).mass r = 0
  · simp only [hr, zero_mul, mul_zero]
  · have hpos : 0 < (p.map prior).mass r :=
      lt_of_le_of_ne ((p.map prior).nonneg r) (Ne.symm hr)
    rw [independent r hpos l xx]
    ring

theorem conditionalIndependent_iff_mass_factorization {R L : Type*}
    [Fintype R] [Fintype L] (p : FiniteLaw A)
    (prior : A → R) (label : A → L) (x : A → X) :
    ConditionalIndependent p prior label x ↔ ConditionalMassFactorization p prior label x :=
  ⟨mass_factorization_of_conditionalIndependent p prior label x,
    conditionalIndependent_of_mass_factorization p prior label x⟩

theorem joint_append_readable_entropy {R L : Type*} [Fintype R] [Fintype L]
    (p : FiniteLaw A) (prior : A → R) (label : A → L) (x : A → X)
    (read : R × X → L) (hread : ∀ a, read (prior a, x a) = label a) :
    finiteEntropy (p.map (fun a => ((prior a, label a), x a))).mass =
      finiteEntropy (p.map (fun a => (prior a, x a))).mass := by
  let lift : R × X → (R × L) × X := fun rx => ((rx.1, read rx), rx.2)
  have hinj : Function.Injective lift := by
    intro a b h
    apply Prod.ext
    · exact congrArg (fun t : (R × L) × X => t.1.1) h
    · exact congrArg (fun t : (R × L) × X => t.2) h
  have hcomp : (fun a => lift (prior a, x a)) =
      (fun a => ((prior a, label a), x a)) := by
    funext a
    simp only [lift, hread]
  have hm := map_comp_mass p (fun a => (prior a, x a)) lift
  rw [hcomp] at hm
  calc
    finiteEntropy (p.map (fun a => ((prior a, label a), x a))).mass =
        finiteEntropy (((p.map (fun a => (prior a, x a))).map lift).mass) := by
      rw [hm]
    _ = _ := (p.map (fun a => (prior a, x a))).map_entropy_of_injective lift hinj

variable {Label : ℕ → Type v} [∀ n, Fintype (Label n)]

def remainingEntropy (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (x : A → X) (n : ℕ) : ℝ :=
  finiteEntropy (p.map (fun a => (labelRecordOf labels n a, x a))).mass -
    finiteEntropy (p.map (labelRecordOf labels n)).mass

@[simp] theorem remainingEntropy_zero (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) :
    remainingEntropy p labels x 0 = finiteEntropy (p.map x).mass := by
  have hm := map_comp_mass p x (fun xx : X => ((PUnit.unit : PUnit.{v + 1}), xx))
  have he : finiteEntropy (p.map (fun a => (labelRecordOf labels 0 a, x a))).mass =
      finiteEntropy (p.map x).mass := by
    change finiteEntropy (p.map (fun a => ((PUnit.unit : PUnit.{v + 1}), x a))).mass =
      finiteEntropy (p.map x).mass
    rw [← hm]
    exact (p.map x).map_entropy_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  have hz : finiteEntropy (p.map (labelRecordOf labels 0)).mass = 0 := by
    change finiteEntropy (p.map (fun _ : A => (PUnit.unit : PUnit.{v + 1}))).mass = 0
    simp [finiteEntropy, FiniteLaw.map_mass, p.total, entropyTerm]
  rw [remainingEntropy, he, hz, sub_zero]

theorem remainingEntropy_complete (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) (depth : ℕ)
    (complete : Function.Injective (labelRecordOf labels depth)) :
    remainingEntropy p labels x depth = 0 := by
  have hi : Function.Injective (fun a => (labelRecordOf labels depth a, x a)) :=
    fun _ _ h => complete (congrArg Prod.fst h)
  rw [remainingEntropy, p.map_entropy_of_injective _ hi,
    p.map_entropy_of_injective _ complete, sub_self]

theorem prefix_entropy_succ (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n < depth) :
    finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass =
      finiteEntropy (p.map (labelRecordOf labels n)).mass +
        (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n := by
  have h := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at h
  exact h

theorem remainingEntropy_succ_readable (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) (depth n : ℕ) (hn : n < depth)
    (read : LabelRecord Label n × X → Label n)
    (hread : ∀ a, read (labelRecordOf labels n a, x a) = labels n a) :
    remainingEntropy p labels x n - remainingEntropy p labels x (n + 1) =
      (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n := by
  have hj := joint_append_readable_entropy p (labelRecordOf labels n) (labels n)
    x read hread
  have hp := prefix_entropy_succ p labels depth n hn
  change finiteEntropy (p.map (fun a => (labelRecordOf labels (n + 1) a, x a))).mass =
    finiteEntropy (p.map (fun a => (labelRecordOf labels n a, x a))).mass at hj
  unfold remainingEntropy
  rw [hj, hp]
  ring

theorem remainingEntropy_succ_independent (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (x : A → X) (n : ℕ)
    (independent : ConditionalIndependent p (labelRecordOf labels n) (labels n) x) :
    remainingEntropy p labels x (n + 1) = remainingEntropy p labels x n := by
  exact conditional_independence_entropy p (labelRecordOf labels n) (labels n) x independent

theorem incident_rate_eq_coordinate_entropy (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (x : A → X)
    (complete : Function.Injective (labelRecordOf labels depth))
    (readable : ∀ n : Fin depth, reader n ≠ .yz →
      ∃ read : LabelRecord Label n.val × X → Label n.val,
        ∀ a, read (labelRecordOf labels n.val a, x a) = labels n.val a)
    (independent : ∀ n : Fin depth, reader n = .yz →
      ConditionalIndependent p (labelRecordOf labels n.val) (labels n.val) x) :
    ConditionalLabels.lawPairingRate p labels depth reader .xy +
      ConditionalLabels.lawPairingRate p labels depth reader .xz =
        finiteEntropy (p.map x).mass := by
  let E := remainingEntropy p labels x
  have hterm (n : Fin depth) :
      (if reader n = .xy then
        (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val else 0) +
      (if reader n = .xz then
        (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val else 0) =
        E n.val - E (n.val + 1) := by
    by_cases hi : reader n = .yz
    · have he := remainingEntropy_succ_independent p labels x n.val (independent n hi)
      simp only [hi, reduceCtorEq, ite_false]
      change 0 + 0 = remainingEntropy p labels x n.val -
        remainingEntropy p labels x (n.val + 1)
      rw [he]
      ring
    · obtain ⟨read, hread⟩ := readable n hi
      have he := remainingEntropy_succ_readable p labels x depth n.val n.isLt read hread
      change _ = remainingEntropy p labels x n.val -
        remainingEntropy p labels x (n.val + 1)
      rw [he]
      cases hr : reader n <;> simp_all
  have htel : ∀ k, (∑ n ∈ Finset.range k, (E n - E (n + 1))) = E 0 - E k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    ConditionalLabels.lawPairingRate p labels depth reader .xy +
        ConditionalLabels.lawPairingRate p labels depth reader .xz =
        ∑ n : Fin depth, (E n.val - E (n.val + 1)) := by
      simp only [ConditionalLabels.lawPairingRate, ConditionalLabels.pairingRate,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun n _ => hterm n)
    _ = E 0 - E depth := by
      calc
        (∑ n : Fin depth, (E n.val - E (n.val + 1))) =
            ∑ n ∈ Finset.range depth, (E n - E (n + 1)) :=
          Fin.sum_univ_eq_sum_range (fun n => E n - E (n + 1)) depth
        _ = E 0 - E depth := htel depth
    _ = finiteEntropy (p.map x).mass := by
      rw [show E 0 = finiteEntropy (p.map x).mass from remainingEntropy_zero p labels x,
        show E depth = 0 from remainingEntropy_complete p labels x depth complete, sub_zero]

theorem nonincident_rate_eq_entropy_sub_coordinate (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (x : A → X)
    (complete : Function.Injective (labelRecordOf labels depth))
    (readable : ∀ n : Fin depth, reader n ≠ .yz →
      ∃ read : LabelRecord Label n.val × X → Label n.val,
        ∀ a, read (labelRecordOf labels n.val a, x a) = labels n.val a)
    (independent : ∀ n : Fin depth, reader n = .yz →
      ConditionalIndependent p (labelRecordOf labels n.val) (labels n.val) x) :
    ConditionalLabels.lawPairingRate p labels depth reader .yz =
      finiteEntropy p.mass - finiteEntropy (p.map x).mass := by
  have hall := ConditionalLabels.lawPairingRate_sum p labels depth reader complete
  have hx := incident_rate_eq_coordinate_entropy p labels depth reader x
    complete readable independent
  linarith

end MatrixMultiplication.DualInformation

end

end OAI
