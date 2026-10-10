import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveResidues

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

lemma dataResidueGood_exists {M m n a : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) : dataResidueGood (trueData M) a m ↔
      ∃ u : (ZMod m)ˣ,a=(u : ZMod m).val ∧
        FavorableUnit (by omega) hb (UniversalSplit.firstComponent hm) u := by
  let : NeZero m := ⟨by omega⟩
  constructor
  · intro h
    have hu : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr h.2.1
    have hv : a=(hu.unit : ZMod m).val := by
      rw [hu.unit_spec,ZMod.val_natCast,Nat.mod_eq_of_lt h.1]
    exact ⟨hu.unit,hv,(dataResidueGood_correct hM hm hb hd hu.unit hv).mp h⟩
  · rintro ⟨u,ha,h⟩
    exact (dataResidueGood_correct hM hm hb hd u ha).mpr h

noncomputable def dataGoodList (data : FactorData) (m n : ℕ)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  ∃ i : Fin (n^5),dataResidueGood data (bitsValue (TransitionWords.read y i)).toNat m
lemma dataGoodList_correct {M m n : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (y : Basis (Completion.transitionWidth n)) :
    dataGoodList (trueData M) m n y ↔
      ListSlots.GoodOutput (by omega) hb (UniversalSplit.firstComponent hm) y := by
  unfold dataGoodList ListSlots.GoodOutput
  apply exists_congr
  intro i
  exact dataResidueGood_exists hM hm hb hd

/-- The source canonical list has the CRT unit in the first field and zero in
all remaining fields (including the final unused word). -/
lemma canonical_list_words {m n : ℕ} (hm : m≠0) (hb : m < 2^n) (p₀ : Component m) :
    ListSlots.canonical hm hb p₀=TransitionWords.encode
      (fun i : Fin (n^5) => natBasis n (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0)) := by
  let : NeZero m := ⟨hm⟩
  unfold ListSlots.canonical ListSlots.ordinary
  congr 1
  funext i
  apply (bitsEquiv n).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue (padBits _ (canonicalList hm p₀ (n^5) i))).toNat=_
  rw [padBits_value]
  simp only [canonicalList,bitsEquiv,Equiv.coe_fn_symm_mk,bitsValue_bits,BitVec.toNat_ofNat,
    ]
  have hv : (if i.val=0 then (canonicalUnit hm p₀ : ZMod m).val else 0) < m := by
    split_ifs
    · exact ZMod.val_lt _
    · omega
  change _=(bitsValue (natBasis n _)).toNat
  rw [natBasis_value,Nat.mod_eq_of_lt (hv.trans_le (Nat.le_pow_clog (by decide) m)),Nat.mod_eq_of_lt (hv.trans hb)]

/-- A direct fixed-field validator: read field zero, test its supplied-factor CRT
congruences, and check every other field and the unused word is zero. -/
noncomputable def dataCanonicalList (data : FactorData) (m n : ℕ) (hn : 0<n)
    (y : Basis (Completion.transitionWidth n)) : Prop :=
  let a := TransitionWords.read y ⟨0,pow_pos hn 5⟩
  dataCanonicalResidue data (bitsValue a).toNat m ∧
    y=TransitionWords.encode (fun i : Fin (n^5) => if i.val=0 then a else natBasis n 0)

lemma basis_eq_natBasis {n a : ℕ} (ha : a<2^n) (x : Basis n) :
    (bitsValue x).toNat=a ↔ x=natBasis n a := by
  constructor
  · intro hx
    apply (bitsEquiv n).injective
    apply BitVec.eq_of_toNat_eq
    change (bitsValue x).toNat=(bitsValue (natBasis n a)).toNat
    rw [hx,natBasis_value,Nat.mod_eq_of_lt ha]
  · intro hx
    rw [hx,natBasis_value,Nat.mod_eq_of_lt ha]

lemma dataCanonicalList_correct {M m n : ℕ} (hM : 0<M) (hm : 2 ≤ m) (hb : m < 2^n)
    (hd : m∣M) (hn : 0<n) (y : Basis (Completion.transitionWidth n)) :
    dataCanonicalList (trueData M) m n hn y ↔
      y=ListSlots.canonical (by omega) hb (UniversalSplit.firstComponent hm) := by
  let : NeZero m := ⟨by omega⟩
  let u := canonicalUnit (by omega : m≠0) (UniversalSplit.firstComponent hm)
  have hu : (u : ZMod m).val<2^n := (ZMod.val_lt _).trans hb
  rw [dataCanonicalList,dataCanonicalResidue_correct hM hm hd,basis_eq_natBasis hu,
    canonical_list_words]
  have hshape : (fun i : Fin (n^5) => natBasis n (if i.val=0 then (u : ZMod m).val else 0))=
      (fun i : Fin (n^5) => if i.val=0 then natBasis n (u : ZMod m).val else natBasis n 0) := by
    funext i
    split_ifs <;> rfl
  change (_=natBasis n (u : ZMod m).val ∧ _) ↔ y=TransitionWords.encode _
  rw [hshape]
  constructor
  · rintro ⟨ha,hy⟩
    simpa only [ha] using hy
  · intro hy
    rw [hy,TransitionWords.read_encode]
    simp only [ite_true,eq_self]
    exact ⟨trivial,rfl⟩

namespace Completion
/-- Equivalent form of dyadic completion for a retrospective, data-based test
of the guessed string. No canonical output is used during preparation. -/
def test {α : Type*} {W t d : ℕ} (good : α→Prop) (guessGood : Basis W→Prop)
    (s z : ℚ) (r : Raw α W t d) : Prop :=
  ordinaryPass good s z r ∨ rare r.1 ∧ guessGood r.2.2.1 ∧
    threshold (guessRetention W t s z) r.2.2.2
lemma test_eq_passed {α : Type*} {W t d : ℕ} (good : α→Prop) (guessGood : Basis W→Prop)
    (y₀ : Basis W) (s z : ℚ) (hg : ∀ y,guessGood y ↔ y=y₀) (r : Raw α W t d) :
    test good guessGood s z r ↔ passed good y₀ s z r := by
  simp only [test,passed,guessPass,hg]
end Completion

noncomputable def dataListPassed {n : ℕ} (data : FactorData) (m : Basis n) (hn : 0<n)
    (r : PhysicalListSlots.Result n) : Prop :=
  Completion.test (fun x => dataGoodList data (bitsValue m).toNat n (PhysicalListSlots.ordinary x))
    (dataCanonicalList data (bitsValue m).toNat n hn)
    (dataListSuccess data (bitsValue m).toNat n (n^5)) (Completion.target n) r

/-- Same integer, same raw outcome, same retention coin. A verified occurrence
record suffices even when the request is only a divisor of that occurrence. -/
lemma dataListPassed_correct {M n : ℕ} (hM : 0<M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M) (hn : 0<n)
    (r : PhysicalListSlots.Result n) :
    dataListPassed (trueData M) m hn r ↔
      PhysicalListSlots.passed m (by omega) (UniversalSplit.firstComponent hm) r := by
  have hg : (fun x => dataGoodList (trueData M) (bitsValue m).toNat n (PhysicalListSlots.ordinary x))=
      (ListSlots.GoodOutput (by omega) (bitsValue m).isLt (UniversalSplit.firstComponent hm) ∘
        PhysicalListSlots.ordinary) := by
    funext x
    exact propext (dataGoodList_correct hM hm (bitsValue m).isLt hd _)
  rw [dataListPassed,hg,dataListSuccess_correct hM (by omega) hd]
  exact Completion.test_eq_passed _ _ _ _ _
    (dataCanonicalList_correct hM hm (bitsValue m).isLt hd hn) r

end ExactQuantumFactoring


end

end OAI
