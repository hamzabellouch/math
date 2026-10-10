import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical

structure DivisorFamily (S : PrimeSystem) (B τ C₀ : ℝ) where
  H : ℝ
  members : Finset ℕ
  H_lower : 1 ≤ H
  H_upper : H ≤ Real.exp (C₀ * B)
  squarefree : ∀ d ∈ members, Squarefree d
  support : ∀ d ∈ members, d.primeFactors ⊆ S.primes
  greater_one : ∀ d ∈ members, 1 < d
  lower : ∀ d ∈ members, H < d
  upper : ∀ d ∈ members, (d : ℝ) ≤ τ * H
  omega : ∀ d ∈ members, d.primeFactors.card ≤ ⌈C₀ * Real.log B⌉₊

structure Specification (S : PrimeSystem) {B τ C₀ : ℝ}
    (D : S.DivisorFamily B τ C₀) (h L : ℕ) where
  length : ℕ
  length_pos : 0 < length
  length_le : length ≤ L
  offset : Fin (length+1) → ℤ
  offset_zero : offset 0 = 0
  offsets_distinct : Function.Injective offset
  label : Fin length → ℕ
  label_mem : ∀ i, label i ∈ D.members
  sign : Fin length → ℤ
  sign_mem : ∀ i, sign i = -1 ∨ sign i = 1
  step : ∀ i, offset i.succ - offset i.castSucc = sign i * h * label i
  extra : S.Index
  extra_not_div : ∀ i, ¬(extra : ℕ) ∣ label i
  suffix : Fin length
  extra_div_suffix : ((extra : ℕ) : ℤ) ∣ offset (Fin.last length) - offset suffix.castSucc

namespace Specification
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

def QualifiesAt (s : S.Specification D h L) (x : ℤ) : Prop :=
  ((s.extra : ℕ) : ℤ) ∣ x ∧ ∀ i, (s.label i : ℤ) ∣ x + s.offset i.castSucc

def primeSupport (s : S.Specification D h L) : Finset ℕ :=
  insert (s.extra : ℕ) (univ.biUnion (fun i => (s.label i).primeFactors))

def ResidueTest (s : S.Specification D h L) (p : S.Index) (b : ℤ)
    (a : ZMod (p : ℕ)) : Prop :=
  ((p : ℕ) = (s.extra : ℕ) → a + (b : ZMod (p : ℕ)) = 0) ∧
  ∀ i, (p : ℕ) ∣ s.label i → a + (b + s.offset i.castSucc : ℤ) = 0

def OrientedSubpath (s t : S.Specification D h L) (start : ℤ) : Prop :=
  ∃ a : ℕ, ∃ ha : a + t.length ≤ s.length,
    (start = s.offset ⟨a, by omega⟩ ∧
      ∀ j : Fin (t.length+1),
        t.offset j = s.offset ⟨a + j.val, by omega⟩ - start) ∨
    (start = s.offset ⟨a + t.length, by omega⟩ ∧
      ∀ j : Fin (t.length+1),
        t.offset j = s.offset ⟨a + t.length - j.val, by omega⟩ - start)

def Primitive (s : S.Specification D h L) : Prop :=
  (∃ x : ℤ, s.QualifiesAt x) ∧
  ¬ ∃ (t : S.Specification D h L) (start x : ℤ),
    t.length < s.length ∧ s.OrientedSubpath t start ∧
    t.primeSupport ⊆ s.primeSupport ∧ s.QualifiesAt x ∧ t.QualifiesAt (x + start)

end Specification

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ : ℕ}

lemma squarefree_int_dvd_iff (d : ℕ) (hd : Squarefree d) (x : ℤ) :
    (d : ℤ) ∣ x ↔ ∀ p ∈ d.primeFactors, (p : ℤ) ∣ x := by
  simp only [Int.natCast_dvd]
  by_cases hx : x.natAbs = 0
  · simp [hx]
  nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hd]
  rw [Nat.prod_primeFactors_dvd_iff hx]
  constructor
  · intro hsub p hp
    exact (Nat.mem_primeFactors.mp (hsub hp)).2.1
  · intro hp p hpd
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hpd).1, hp p hpd, hx⟩

lemma Specification.qualifies_iff_residueTests (s : S.Specification D h L) (x b : ℤ) :
    s.QualifiesAt (x+b) ↔
      ∀ p : S.Index, s.ResidueTest p b (x : ZMod (p : ℕ)) := by
  simp only [Specification.QualifiesAt, Specification.ResidueTest]
  constructor
  · rintro ⟨hextra, hedge⟩ p
    constructor
    · intro heq
      have hz : ((p : ℕ) : ℤ) ∣ x+b := by simpa only [heq] using hextra
      simpa only [Int.cast_add] using (ZMod.intCast_zmod_eq_zero_iff_dvd (x+b) p).mpr hz
    · intro i hpi
      have hz : ((p : ℕ) : ℤ) ∣ x+b+s.offset i.castSucc :=
        dvd_trans (by exact_mod_cast hpi) (hedge i)
      simpa only [Int.cast_add, add_assoc] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd (x+b+s.offset i.castSucc) p).mpr hz
  · intro hp
    constructor
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x+b) s.extra).mp (by
        simpa only [Int.cast_add] using (hp s.extra).1 rfl)
    · intro i
      apply (squarefree_int_dvd_iff (s.label i) (D.squarefree _ (s.label_mem i)) _).mpr
      intro p hpd
      let q : S.Index := ⟨p, D.support _ (s.label_mem i) hpd⟩
      have hq := (hp q).2 i (Nat.mem_primeFactors.mp hpd).2.1
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (x+b+s.offset i.castSucc) p).mp (by
        simpa only [Int.cast_add, add_assoc] using hq)

abbrev TraceVertices (w : ClosedLine h ℓ) := {b : ℤ // b ∈ univ.image w.offset}

structure AttachedSpec (w : ClosedLine h ℓ) (D : S.DivisorFamily B τ C₀) (L : ℕ) where
  index : Fin (ℓ+1)
  spec : S.Specification D h L
  primitive : spec.Primitive

def AttachedSpec.vertex {line : ClosedLine h ℓ} (s : AttachedSpec line D L) : ℤ :=
  line.offset s.index

def listLocal (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (a : ZMod (p : ℕ)) : ℝ :=
  if ∀ s ∈ 𝔏, s.spec.ResidueTest p s.vertex a then 1 else 0

def listIndicator (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (r : S.Residues) : ℝ :=
  if ∀ s ∈ 𝔏, ∀ p : S.Index, s.spec.ResidueTest p s.vertex (r p) then 1 else 0

lemma listIndicator_product (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (r : S.Residues) :
    listIndicator w 𝔏 r = ∏ p, listLocal w 𝔏 p (r p) := by
  by_cases H : ∀ s ∈ 𝔏, ∀ p : S.Index, s.spec.ResidueTest p s.vertex (r p)
  · rw [listIndicator, ite_eq_left H]
    symm
    apply prod_eq_one
    intro p _
    exact ite_eq_left (fun spec hspec => H spec hspec p)
  · have hp : ∃ p : S.Index, ¬∀ s ∈ 𝔏, s.spec.ResidueTest p s.vertex (r p) := by
      by_contra hp
      push Not at hp
      exact H (fun s hs p => hp p s hs)
    obtain ⟨p, hp⟩ := hp
    rw [listIndicator, ite_eq_right H]
    symm
    exact prod_eq_zero (mem_univ p) (by simp [listLocal, hp])

lemma listLocal_nonneg (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L))
    (p : S.Index) (a : ZMod (p : ℕ)) : 0 ≤ listLocal w 𝔏 p a := by
  unfold listLocal
  split_ifs <;> norm_num

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
