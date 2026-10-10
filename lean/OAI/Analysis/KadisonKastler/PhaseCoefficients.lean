import OAI.Analysis.KadisonKastler.LabelCharacters

namespace OAI

/-!
# Actual coefficients of the finite phase words

The coefficients are indexed by label multisets, so words with the same
phase monomial are grouped before applying Parseval. Their supports are
the sums of precisely the projections whose labels occur in the multiset.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Removing one marked label identifies marked multisets with a label
and a multiset of one smaller cardinality. The mark has no multiplicity. -/
def markedSymEquiv (r : ℕ) :
    (Σ s : Sym ι (r + 1), {a : ι // a ∈ s}) ≃ (ι × Sym ι r) :=
  Equiv.ofBijective (fun x => (x.2.1, x.1.erase x.2.1 x.2.2)) (by
    constructor
    · rintro ⟨s, a, ha⟩ ⟨t, b, hb⟩ h
      obtain ⟨hab, hst⟩ := Prod.mk.inj h
      change a = b at hab
      change s.erase a ha = t.erase b hb at hst
      subst b
      have hst' : s = t := by
        rw [← Sym.cons_erase ha, ← Sym.cons_erase hb, hst]
      subst t
      rfl
    · rintro ⟨a, s⟩
      refine ⟨⟨Sym.cons a s, ⟨a, Sym.mem_cons_self a s⟩⟩, ?_⟩
      simp)

theorem sum_markedSym {B : Type*} [AddCommMonoid B] (r : ℕ)
    (f : ι → Sym ι r → B) :
    (∑ s : Sym ι (r + 1), ∑ a : {a : ι // a ∈ s}, f a.1 (s.erase a.1 a.2)) =
      ∑ a : ι, ∑ s : Sym ι r, f a s := by
  rw [← Fintype.sum_sigma', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (markedSymEquiv r) _ _ (fun _ => rfl)

variable {A : Type*} [Ring A] [Algebra ℂ A]

def phaseSupport (e : ι → A) (s : Multiset ι) : A := ∑ a ∈ s.toFinset, e a

/-- The degree-zero convention allows the positive coefficients to be
defined by removing a first label. -/
def positivePhaseCoefficient (e : ι → A) (v : A) : (r : ℕ) → Sym ι r → A
  | 0, _ => 1
  | r + 1, s => ∑ a : {a : ι // a ∈ s},
      e a.1 * (if r = 0 then 1 else v) * positivePhaseCoefficient e v r (s.erase a.1 a.2)

def positivePhaseProduct (t v : A) : ℕ → A
  | 0 => 1
  | r + 1 => t * (if r = 0 then 1 else v) * positivePhaseProduct t v r

theorem positivePhaseCoefficient_mem (S : Subalgebra ℂ A) (e : ι → A) (v : A)
    (he : ∀ a, e a ∈ S) (hv : v ∈ S) (r : ℕ) (s : Sym ι r) :
    positivePhaseCoefficient e v r s ∈ S := by
  induction r with
  | zero => exact S.one_mem
  | succ r ih =>
    apply S.sum_mem
    intro a _
    apply S.mul_mem
    · apply S.mul_mem (he a.1)
      split_ifs
      · exact S.one_mem
      · exact hv
    · exact ih _

omit [Algebra ℂ A] in
theorem positivePhaseProduct_succ (t v : A) (r : ℕ) :
    positivePhaseProduct t v (r + 1) = (t * v) ^ r * t := by
  induction r with
  | zero => simp [positivePhaseProduct]
  | succ r ih =>
    simp only [positivePhaseProduct, Nat.add_one_ne_zero, ite_false] at *
    rw [ih, pow_succ']
    simp only [mul_assoc]

variable {q : ℕ} [NeZero q]

def diagonalPhase (e : ι → A) (θ : ι → ZMod q) : A :=
  ∑ a, ZMod.stdAddChar (θ a) • e a

theorem positivePhase_expansion (e : ι → A) (v : A) (r : ℕ) (θ : ι → ZMod q) :
    positivePhaseProduct (diagonalPhase e θ) v r =
      ∑ s : Sym ι r, multisetCharacter (s : Multiset ι) θ •
        positivePhaseCoefficient e v r s := by
  induction r with
  | zero =>
    have hs (s : Sym ι 0) : (s : Multiset ι) = 0 := by
      rw [Sym.eq_nil_of_card_zero s]
      rfl
    simp [positivePhaseProduct, positivePhaseCoefficient, hs, multisetCharacter]
  | succ r ih =>
    rw [positivePhaseProduct, ih]
    symm
    calc
      _ = ∑ s : Sym ι (r + 1), ∑ a : {a : ι // a ∈ s},
          (ZMod.stdAddChar (θ a.1) * multisetCharacter (s.erase a.1 a.2 : Multiset ι) θ) •
            (e a.1 * (if r = 0 then 1 else v) *
              positivePhaseCoefficient e v r (s.erase a.1 a.2)) := by
        apply sum_congr rfl
        intro s _
        rw [positivePhaseCoefficient, smul_sum]
        apply sum_congr rfl
        intro a _
        congr 1
        conv_lhs => rw [← Sym.cons_erase a.2]
        exact multisetCharacter_cons _ _ _
      _ = ∑ a : ι, ∑ s : Sym ι r,
          (ZMod.stdAddChar (θ a) * multisetCharacter (s : Multiset ι) θ) •
            (e a * (if r = 0 then 1 else v) * positivePhaseCoefficient e v r s) :=
        sum_markedSym (B := A) r (fun a s =>
          (ZMod.stdAddChar (θ a) * multisetCharacter (s : Multiset ι) θ) •
            (e a * (if r = 0 then 1 else v) * positivePhaseCoefficient e v r s))
      _ = _ := by
        simp only [diagonalPhase, sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm,
          mul_assoc]
        rw [sum_comm]
        simp only [smul_sum, smul_smul]
        apply sum_congr rfl
        intro s _
        apply sum_congr rfl
        intro a _
        rw [mul_comm (ZMod.stdAddChar (θ a))]

theorem positivePhase_power_expansion (e : ι → A) (v : A) (r : ℕ)
    (θ : ι → ZMod q) :
    (diagonalPhase e θ * v) ^ r * diagonalPhase e θ =
      ∑ s : Sym ι (r + 1), multisetCharacter (s : Multiset ι) θ •
        positivePhaseCoefficient e v (r + 1) s := by
  rw [← positivePhaseProduct_succ]
  exact positivePhase_expansion e v (r + 1) θ

omit [NeZero q] [Fintype ι] [Algebra ℂ A] in
theorem phaseSupport_mul_label (e : ι → A)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (s : Multiset ι) (a : ι) (ha : a ∈ s) : phaseSupport e s * e a = e a := by
  simp only [phaseSupport, sum_mul, hmul]
  simp [ha]

omit [NeZero q] [Fintype ι] [Algebra ℂ A] in
theorem label_mul_phaseSupport (e : ι → A)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (s : Multiset ι) (a : ι) (ha : a ∈ s) : e a * phaseSupport e s = e a := by
  simp only [phaseSupport, mul_sum, hmul]
  simp [ha]

omit [NeZero q] [Algebra ℂ A] in
theorem positivePhaseCoefficient_left_support (e : ι → A) (v : A)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (r : ℕ) (s : Sym ι (r + 1)) :
    phaseSupport e (s : Multiset ι) * positivePhaseCoefficient e v (r + 1) s =
      positivePhaseCoefficient e v (r + 1) s := by
  rw [positivePhaseCoefficient, mul_sum]
  apply sum_congr rfl
  intro a _
  simpa only [mul_assoc] using
    congrArg (fun x : A => x * (if r = 0 then 1 else v) *
      positivePhaseCoefficient e v r (s.erase a.1 a.2))
      (phaseSupport_mul_label e hmul (s : Multiset ι) a.1 a.2)

omit [NeZero q] [Algebra ℂ A] in
theorem positivePhaseCoefficient_right_support_of_subset (e : ι → A) (v : A)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (r : ℕ) (s : Sym ι (r + 1)) (t : Multiset ι)
    (hst : ∀ a ∈ s, a ∈ t) :
    positivePhaseCoefficient e v (r + 1) s * phaseSupport e t =
      positivePhaseCoefficient e v (r + 1) s := by
  induction r with
  | zero =>
    simp only [positivePhaseCoefficient, ite_true, mul_one, sum_mul]
    apply sum_congr rfl
    intro a _
    exact label_mul_phaseSupport e hmul _ a.1 (hst a.1 a.2)
  | succ r ih =>
    rw [positivePhaseCoefficient, sum_mul]
    apply sum_congr rfl
    intro a _
    rw [mul_assoc, ih]
    intro b hb
    exact hst b (Multiset.mem_of_mem_erase hb)

omit [NeZero q] [Algebra ℂ A] in
/-- Every positive coefficient has right support in its label multiset. -/
theorem positivePhaseCoefficient_right_support (e : ι → A) (v : A)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (r : ℕ) (s : Sym ι (r + 1)) :
    positivePhaseCoefficient e v (r + 1) s * phaseSupport e (s : Multiset ι) =
      positivePhaseCoefficient e v (r + 1) s :=
  positivePhaseCoefficient_right_support_of_subset e v hmul r s _ (fun _ h => h)

section Star

variable [StarRing A] [StarModule ℂ A]

omit [NeZero q] [Fintype ι] [Algebra ℂ A] [StarModule ℂ A] in
theorem phaseSupport_star (e : ι → A) (he : ∀ a, star (e a) = e a) (s : Multiset ι) :
    star (phaseSupport e s) = phaseSupport e s := by
  simp only [phaseSupport, star_sum, he]

def negativePhaseCoefficient (e : ι → A) (v : A) (r : ℕ) (s : Sym ι r) : A :=
  star v * star (positivePhaseCoefficient e v r s)

theorem negativePhase_power_expansion (e : ι → A) (v : A) (r : ℕ)
    (θ : ι → ZMod q) :
    (star v * star (diagonalPhase e θ)) ^ (r + 1) =
      ∑ s : Sym ι (r + 1), ((multisetCharacter (s : Multiset ι))⁻¹ :
        AddChar (ι → ZMod q) ℂ) θ •
        negativePhaseCoefficient e v (r + 1) s := by
  have h := congrArg (fun x : A => star v * star x)
    (positivePhase_power_expansion e v r θ)
  simpa only [star_mul, star_pow, ← mul_assoc, ← pow_succ', star_sum, mul_sum,
    star_smul, negativePhaseCoefficient, mul_smul_comm, AddChar.inv_apply',
    AddChar.inv_apply_eq_conj, RCLike.star_def] using h

omit [NeZero q] [Algebra ℂ A] [StarModule ℂ A] in
/-- Taking the adjoint switches the positive left support into the
negative right support. -/
theorem negativePhaseCoefficient_right_support (e : ι → A) (v : A)
    (he : ∀ a, star (e a) = e a)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (r : ℕ) (s : Sym ι (r + 1)) :
    negativePhaseCoefficient e v (r + 1) s * phaseSupport e (s : Multiset ι) =
      negativePhaseCoefficient e v (r + 1) s := by
  have h := congrArg star (positivePhaseCoefficient_left_support e v hmul r s)
  rw [star_mul, phaseSupport_star e he] at h
  exact (mul_assoc _ _ _).trans (congrArg (fun x => star v * x) h)

theorem diagonalPhase_mem_unitary (e : ι → A)
    (he : ∀ a, star (e a) = e a)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (hsum : ∑ a, e a = 1) (θ : ι → ZMod q) :
    diagonalPhase e θ ∈ unitary A := by
  have hstar (a : ι) :
      star (ZMod.stdAddChar (θ a)) * ZMod.stdAddChar (θ a) = 1 := by
    change starRingEnd ℂ (ZMod.stdAddChar (θ a)) * ZMod.stdAddChar (θ a) = 1
    rw [← AddChar.inv_apply_eq_conj]
    exact inv_mul_cancel₀ (by simp [ZMod.stdAddChar_apply])
  have hstar' (a : ι) :
      ZMod.stdAddChar (θ a) * star (ZMod.stdAddChar (θ a)) = 1 := by
    rw [mul_comm]
    exact hstar a
  constructor
  · simp only [diagonalPhase, star_sum, star_smul, he, sum_mul, mul_sum,
      smul_mul_assoc, mul_smul_comm, hmul, smul_ite, smul_zero]
    simpa only [sum_ite_eq', mem_univ, ite_true, smul_smul, hstar', one_smul] using hsum
  · simp only [diagonalPhase, star_sum, star_smul, he, sum_mul, mul_sum,
      smul_mul_assoc, mul_smul_comm, hmul, smul_ite, smul_zero]
    simpa only [sum_ite_eq', mem_univ, ite_true, smul_smul, hstar, one_smul] using hsum

end Star

section Operators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual positive word coefficients form an isometric column. -/
theorem positivePhaseCoefficient_column_norm (e : ι → H →L[ℂ] H)
    (he : ∀ a, star (e a) = e a)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (hsum : ∑ a, e a = 1) (v : H →L[ℂ] H) (hv : v ∈ unitary (H →L[ℂ] H))
    (r : ℕ) (hr : r + 1 < q) (x : H) :
    ‖WithLp.toLp 2 (fun s : Sym ι (r + 1) => positivePhaseCoefficient e v (r + 1) s x)‖ =
      ‖x‖ := by
  apply unitary_phase_coefficient_column
    (fun s : Sym ι (r + 1) => multisetCharacter (q := q) (s : Multiset ι))
    (additiveCharacters_orthogonal _ (multisetCharacter_injective hr))
    (positivePhaseCoefficient e v (r + 1))
  intro θ
  rw [← positivePhase_power_expansion]
  have ht := diagonalPhase_mem_unitary e he hmul hsum θ
  exact (unitary (H →L[ℂ] H)).mul_mem
    ((unitary (H →L[ℂ] H)).pow_mem ((unitary (H →L[ℂ] H)).mul_mem ht hv) r) ht

/-- The inverse phase characters give the same isometric column for the
negative powers. -/
theorem negativePhaseCoefficient_column_norm (e : ι → H →L[ℂ] H)
    (he : ∀ a, star (e a) = e a)
    (hmul : ∀ a b, e a * e b = if a = b then e a else 0)
    (hsum : ∑ a, e a = 1) (v : H →L[ℂ] H) (hv : v ∈ unitary (H →L[ℂ] H))
    (r : ℕ) (hr : r + 1 < q) (x : H) :
    ‖WithLp.toLp 2 (fun s : Sym ι (r + 1) => negativePhaseCoefficient e v (r + 1) s x)‖ =
      ‖x‖ := by
  apply unitary_phase_coefficient_column
    (fun s : Sym ι (r + 1) => ((multisetCharacter (s : Multiset ι))⁻¹ :
      AddChar (ι → ZMod q) ℂ))
    (additiveCharacters_orthogonal _ (inv_injective.comp (multisetCharacter_injective hr)))
    (negativePhaseCoefficient e v (r + 1))
  intro θ
  rw [← negativePhase_power_expansion]
  have ht := diagonalPhase_mem_unitary e he hmul hsum θ
  exact (unitary (H →L[ℂ] H)).pow_mem
    ((unitary (H →L[ℂ] H)).mul_mem (Unitary.star_mem hv) (Unitary.star_mem ht)) (r + 1)

end Operators

end

end KadisonKastler

end OAI
