import OAI.Geometry.PeriodicTiling.LabeledDigitBlocks
import OAI.Geometry.PeriodicTiling.CyclicCRT

namespace OAI

universe uK uA uB uL uJ uF

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

abbrev ChannelOtherDigits (i : Channel p) (j : Label p i) :=
  ∀ q : {q : Label p i // q ≠ j}, ZMod (E.digitPrime i q)

abbrev ChannelBlockA (i : Channel p) (j : Label p i) :=
  Fin (E.blockA i j) × ChannelOtherDigits E i j

abbrev ChannelBlockB (i : Channel p) (j : Label p i) :=
  Fin (E.blockB i j) × ChannelOtherDigits E i j

def channelDigitBase (i : Channel p) (j : Label p i) :
    LabeledBlocks (ZMod (E.digitPrime i j)) (Fin (E.blockA i j))
      (Fin (E.blockB i j)) (E.a i) (E.b i) :=
  LabeledBlocks.digit (E.a i) (E.b i) (E.digitPrime i j)
    (E.blockA i j) (E.blockB i j) (E.digit_eq i j)

def channelDigitBlocks (i : Channel p) (j : Label p i) :
    LabeledBlocks (ZMod (E.r i)) (ChannelBlockA E i j)
      (ChannelBlockB E i j) (E.a i) (E.b i) :=
  (LabeledBlocks.onCoordinate (fun q => ZMod (E.digitPrime i q)) j
    (channelDigitBase E i j)).transport (digitEquiv E i).toEquiv

@[simp] theorem channelDigitBlocks_C (i : Channel p) (j : Label p i)
    (w : ZMod (E.r i)) :
    (channelDigitBlocks E i j).C w =
      (channelDigitBase E i j).C (digitEquiv E i w j) := by
  simp [channelDigitBlocks]

theorem channelDigitBlocks_C_eq (i : Channel p) (j : Label p i)
    {w w' : ZMod (E.r i)} (h : digitEquiv E i w j = digitEquiv E i w' j) :
    (channelDigitBlocks E i j).C w = (channelDigitBlocks E i j).C w' := by
  simp only [channelDigitBlocks_C, h]

theorem channelDigitBlocks_active_iff (i : Channel p) (j q : Label p i) :
    (∃ w w' : ZMod (E.r i), w - w' ∈ digitSubgroup E i q ∧
      (channelDigitBlocks E i j).C w ≠ (channelDigitBlocks E i j).C w') ↔ q = j := by
  constructor
  · rintro ⟨w, w', hdiff, hne⟩
    by_contra hq
    apply hne
    exact channelDigitBlocks_C_eq E i j
      ((sub_mem_digitSubgroup_iff E i q w w').1 hdiff j (Ne.symm hq))
  · intro hq
    subst q
    let : Fact (1 < E.a i) := ⟨(E.a_prime i).one_lt⟩
    let : Fact (1 < E.b i) := ⟨(E.b_prime i).one_lt⟩
    obtain ⟨x, y, hxy, hne⟩ :=
      LabeledBlocks.C_designated_witness (fun q => ZMod (E.digitPrime i q)) j
        (channelDigitBase E i j)
    refine ⟨(digitEquiv E i).symm x, (digitEquiv E i).symm y, ?_, ?_⟩
    · apply (sub_mem_digitSubgroup_iff E i j _ _).2
      simpa only [AddEquiv.apply_symm_apply] using hxy
    · simpa only [channelDigitBlocks_C, AddEquiv.apply_symm_apply,
        LabeledBlocks.C_onCoordinate] using hne

namespace LabeledBlocks

def castSizes {K : Type uK} {A : Type uA} {B : Type uB} {a b a' b' : ℕ}
    (D : LabeledBlocks K A B a b)
    (ha : a = a') (hb : b = b') : LabeledBlocks K A B a' b' := by
  subst a'
  subst b'
  exact D

@[simp] theorem T_transport_apply {K : Type uK} {L : Type uL} {A : Type uA} {B : Type uB} {a b : ℕ}
    (D : LabeledBlocks K A B a b) (e : L ≃ K) (t : ℤ) (x : L) :
    (D.transport e).T t x = e.symm (D.T t (e x)) := rfl

theorem T_onCoordinate {J : Type uJ} [DecidableEq J] (F : J → Type uF) (j : J)
    {A : Type uA} {B : Type uB} {a b : ℕ} (D : LabeledBlocks (F j) A B a b) (t : ℤ) (x : ∀ q, F q) :
    (onCoordinate F j D).T t x =
      (Equiv.piSplitAt j F).symm (D.T t (x j), fun q => x q) := by
  rw [onCoordinate, T_transport_apply, T_copyRight]
  rfl

theorem T_onCoordinate_other {J : Type uJ} [DecidableEq J] (F : J → Type uF) (j : J)
    {A : Type uA} {B : Type uB} {a b : ℕ} (D : LabeledBlocks (F j) A B a b) (t : ℤ)
    (x : ∀ q, F q) (q : J) (hq : q ≠ j) :
    (onCoordinate F j D).T t x q = x q := by
  rw [T_onCoordinate]
  simp [Equiv.piSplitAt, hq]

theorem T_onCoordinate_transport_other {J : Type uJ} {L : Type uL} [DecidableEq J]
    (F : J → Type uF) (j : J) {A : Type uA} {B : Type uB} {a b : ℕ}
    (D : LabeledBlocks (F j) A B a b) (e : L ≃ (∀ q, F q)) (t : ℤ)
    (x : L) (q : J) (hq : q ≠ j) :
    e (((onCoordinate F j D).transport e).T t x) q = e x q := by
  rw [T_transport_apply, Equiv.apply_symm_apply]
  exact T_onCoordinate_other F j D t (e x) q hq

end LabeledBlocks

theorem channelDigitBlocks_T_other (i : Channel p) (j : Label p i) (t : ℤ)
    (w : ZMod (E.r i)) (q : Label p i) (hq : q ≠ j) :
    digitEquiv E i ((channelDigitBlocks E i j).T t w) q = digitEquiv E i w q := by
  simpa only [channelDigitBlocks, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv] using
    (LabeledBlocks.T_onCoordinate_transport_other
      (fun q : Label p i => ZMod (E.digitPrime i q)) j
      (channelDigitBase E i j) (digitEquiv E i).toEquiv t w q hq)

def seedOneBlocks :
    LabeledBlocks (ZMod (E.r (.inr (0 : Fin 2))))
      (ChannelBlockA E (.inr 0) ()) (ChannelBlockB E (.inr 0) ())
      2 (E.b (.inr 0)) :=
  (channelDigitBlocks E (.inr 0) ()).castSizes
    (by simpa using E.seed_a (0 : Fin 2)) rfl

def seedTwoBlocks :
    LabeledBlocks (ZMod (E.r (.inr (1 : Fin 2))))
      (ChannelBlockA E (.inr 1) ()) (ChannelBlockB E (.inr 1) ())
      3 (E.b (.inr 1)) :=
  (channelDigitBlocks E (.inr 1) ()).castSizes
    (by simpa using E.seed_a (1 : Fin 2)) rfl

end PeriodicTilingThree

end

end OAI
