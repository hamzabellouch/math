import OAI.Geometry.PeriodicTiling.CyclicTypes
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Equiv.Basic

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

variable {p : ℕ} [NeZero p]

namespace EncodingParameters

variable (E : EncodingParameters p)

def blockModulus (i : Channel p) : ℕ := (E.r i) ^ 2 * E.a i * E.b i
def cyclicOrder : ℕ := p ^ 4 * ∏ i : Channel p, E.blockModulus i

theorem blockModulus_pos (i : Channel p) : 0 < E.blockModulus i :=
  Nat.mul_pos (Nat.mul_pos (pow_pos (E.r_pos i) 2) (E.a_pos i)) (E.b_pos i)

theorem cyclicOrder_pos : 0 < E.cyclicOrder :=
  Nat.mul_pos (pow_pos E.p_prime.pos 4)
    (Finset.prod_pos (fun i _ => E.blockModulus_pos i))

instance blockModulus_neZero (i : Channel p) : NeZero (E.blockModulus i) :=
  ⟨(E.blockModulus_pos i).ne'⟩
instance cyclicOrder_neZero : NeZero E.cyclicOrder := ⟨E.cyclicOrder_pos.ne'⟩

theorem a_coprime_b_all
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    (i j : Channel p) : Nat.Coprime (E.a i) (E.b j) := by
  apply E.prime_coprime
  simp

theorem a_pairwise_coprime
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : Pairwise (fun i j : Channel p => Nat.Coprime (E.a i) (E.a j)) := by
  intro i j hij
  apply E.prime_coprime
  simpa using hij

theorem b_pairwise_coprime
    {p : ℕ} [NeZero p] (E : EncodingParameters p)
    : Pairwise (fun i j : Channel p => Nat.Coprime (E.b i) (E.b j)) := by
  intro i j hij
  apply E.prime_coprime
  simpa using hij

theorem blockModulus_pairwise :
    Pairwise (fun i j : Channel p => Nat.Coprime (E.blockModulus i) (E.blockModulus j)) := by
  intro i j hij
  have hrr := (E.r_pairwise_coprime hij).pow 2 2
  have hra := (E.r_coprime_a i j).pow_left 2
  have hrb := (E.r_coprime_b i j).pow_left 2
  have har := (E.r_coprime_a j i).symm.pow_right 2
  have haa := E.a_pairwise_coprime hij
  have hab := E.a_coprime_b_all i j
  have hbr := (E.r_coprime_b j i).symm.pow_right 2
  have hba := (E.a_coprime_b_all j i).symm
  have hbb := E.b_pairwise_coprime hij
  simp only [blockModulus, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
  exact ⟨⟨⟨⟨hrr, har⟩, hbr⟩, ⟨⟨hra, haa⟩, hba⟩⟩, ⟨⟨hrb, hab⟩, hbb⟩⟩

theorem p_coprime_blockModulus (i : Channel p) :
    Nat.Coprime p (E.blockModulus i) := by
  have hr := (E.r_coprime_p i).symm.pow_right 2
  have ha : Nat.Coprime p (E.a i) := (E.prime_coprime_p (.inl i)).symm
  have hb : Nat.Coprime p (E.b i) := (E.prime_coprime_p (.inr (.inl i))).symm
  simp only [blockModulus, Nat.coprime_mul_iff_right]
  exact ⟨⟨hr, ha⟩, hb⟩

theorem p4_coprime_blocks :
    Nat.Coprime (p ^ 4) (∏ i : Channel p, E.blockModulus i) := by
  apply Nat.coprime_fintype_prod_right_iff.mpr
  intro i
  exact (E.p_coprime_blockModulus i).pow_left 4

end EncodingParameters

variable (E : EncodingParameters p)

def channelCRT (i : Channel p) :
    ZMod (E.blockModulus i) ≃+ (ZMod ((E.r i) ^ 2) × P E i) := by
  have hRA : Nat.Coprime ((E.r i) ^ 2) (E.a i) := (E.r_coprime_a i i).pow_left 2
  have hRAB : Nat.Coprime ((E.r i) ^ 2 * E.a i) (E.b i) :=
    Nat.coprime_mul_iff_left.mpr ⟨(E.r_coprime_b i i).pow_left 2, E.a_coprime_b i⟩
  exact ((ZMod.chineseRemainder hRAB).toAddEquiv.trans
    (AddEquiv.prodCongr (ZMod.chineseRemainder hRA).toAddEquiv
      (AddEquiv.refl (ZMod (E.b i))))).trans AddEquiv.prodAssoc

def cyclicToFiniteFactor : ZMod E.cyclicOrder ≃+ V E :=
  (ZMod.chineseRemainder E.p4_coprime_blocks).toAddEquiv.trans
    (AddEquiv.prodCongr (AddEquiv.refl (ZMod (p ^ 4)))
      ((ZMod.prodEquivPi E.blockModulus E.blockModulus_pairwise).toAddEquiv.trans
        (AddEquiv.piCongrRight (fun i => channelCRT E i))))

def finiteFactorEquiv : V E ≃+ ZMod E.cyclicOrder := (cyclicToFiniteFactor E).symm

def ambientCyclicEquiv : Ambient E ≃+ (Plane × ZMod E.cyclicOrder) :=
  AddEquiv.prodCongr (AddEquiv.refl Plane) (finiteFactorEquiv E)

end PeriodicTilingThree

end

end OAI
