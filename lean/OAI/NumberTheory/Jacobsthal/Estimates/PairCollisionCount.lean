import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

noncomputable def sum {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a b : R) : ℂ :=
  ∑ u : Rˣ, ψ (a * (u : R) + b * (↑u⁻¹ : R))

noncomputable def standardSum (N : ℕ) [NeZero N] (h k : ℤ) : ℂ :=
  sum ZMod.stdAddChar (h : ZMod N) (k : ZMod N)

theorem sum_swap {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a b : R) : sum ψ a b = sum ψ b a := by
  have h := Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => ψ (a * (u : R) + b * (↑u⁻¹ : R)))
  simpa only [Equiv.inv_apply, inv_inv, add_comm, sum] using h.symm

theorem sum_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (a b : R) (c : Rˣ) :
    sum ψ (a * c) (b * (↑c⁻¹ : R)) = sum ψ a b := by
  have h := Equiv.sum_comp (Equiv.mulLeft c)
    (fun u : Rˣ => ψ (a * (u : R) + b * (↑u⁻¹ : R)))
  simpa only [sum, Equiv.coe_mulLeft, mul_inv_rev, Units.val_mul,
    mul_assoc, mul_comm, mul_left_comm] using h

theorem sum_ringEquiv {R S : Type*} [CommRing R] [Fintype R] [CommRing S] [Fintype S]
    (e : R ≃+* S) (ψ : AddChar S ℂ) (a b : R) :
    sum (ψ.compAddMonoidHom e.toAddMonoidHom) a b = sum ψ (e a) (e b) := by
  have h := Equiv.sum_comp (Units.mapEquiv e.toMulEquiv).toEquiv
    (fun u : Sˣ => ψ (e a * (u : S) + e b * (↑u⁻¹ : S)))
  simpa [sum, ← map_inv] using h

theorem sum_zero_zero {R : Type*} [CommRing R] [Fintype R] (ψ : AddChar R ℂ) :
    sum ψ 0 0 = Fintype.card Rˣ := by simp [sum]

theorem standardSum_exp (N : ℕ) [NeZero N] (h k : ℤ) :
    standardSum N h k = ∑ u : (ZMod N)ˣ,
      Complex.exp (2 * Real.pi * Complex.I *
        ((h : ℂ) * (u.val.val : ℂ) + (k : ℂ) * (u⁻¹).val.val) / N) := by
  unfold standardSum sum
  refine Finset.sum_congr ?_ ?_
  · ext u; simp
  intro u _
  have heq : (h : ZMod N) * u.val + (k : ZMod N) * (u⁻¹).val =
      ((h * (u.val.val : ℤ) + k * ((u⁻¹).val.val : ℤ) : ℤ) : ZMod N) := by simp
  rw [heq, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

end ErdosKloosterman

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

noncomputable def integerWeight (N : ℕ) [NeZero N] (I : Finset ℤ) (h : ZMod N) : ℂ :=
  ∑ x ∈ I, ZMod.stdAddChar (-h*(x : ZMod N))

noncomputable def unitClass (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) : Finset (ZMod N)ˣ :=
  Finset.univ.filter fun u => ZMod.unitsMap hT u = a

noncomputable def restrictedSum (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (h k : ZMod N) : ℂ :=
  ∑ u ∈ unitClass N T hT a,
    ZMod.stdAddChar (h*(u : ZMod N) + k*(c : ZMod N)*(↑u⁻¹ : ZMod N))

noncomputable def hyperbolaPairs (N T : ℕ) [NeZero N] [NeZero T]
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) (I J : Finset ℤ) : Finset (ℤ × ℤ) :=
  (I.product J).filter fun xy =>
    (xy.1 : ZMod N)*(xy.2 : ZMod N) = (c : ZMod N) ∧
      (xy.1 : ZMod T) = (a : ZMod T)

noncomputable def integerFibre (N : ℕ) (I : Finset ℤ) (u : ZMod N) : Finset ℤ :=
  I.filter fun x => (x : ZMod N) = u

noncomputable def pairFibre (N : ℕ) [NeZero N] (c u : (ZMod N)ˣ) (I J : Finset ℤ) :
    Finset (ℤ × ℤ) :=
  (integerFibre N I (u : ZMod N)).product
    (integerFibre N J ((c : ZMod N)*(↑u⁻¹ : ZMod N)))

@[simp] theorem mem_unitClass (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (u : (ZMod N)ˣ) :
    u ∈ unitClass N T hT a ↔ ZMod.unitsMap hT u = a := by simp [unitClass]

@[simp] theorem mem_integerFibre (N : ℕ) (I : Finset ℤ) (u : ZMod N) (x : ℤ) :
    x ∈ integerFibre N I u ↔ x ∈ I ∧ (x : ZMod N) = u := by simp [integerFibre]

theorem unit_class_of_int (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (u : (ZMod N)ˣ) (x : ℤ) (hx : (u : ZMod N) = (x : ZMod N)) :
    ZMod.unitsMap hT u = a ↔ (x : ZMod T) = (a : ZMod T) := by
  rw [← Units.val_inj]
  change (ZMod.castHom hT (ZMod T)) (u : ZMod N) = (a : ZMod T) ↔ _
  rw [hx, map_intCast]

end ErdosHyperbolaIdentities

end

section

open scoped BigOperators

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

noncomputable def productChar {R S : Type*} [AddMonoid R] [AddMonoid S]
    (ψ : AddChar R ℂ) (φ : AddChar S ℂ) : AddChar (R × S) ℂ where
  toFun x := ψ x.1 * φ x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

theorem sum_product {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (ψ : AddChar R ℂ) (φ : AddChar S ℂ)
    (a b : R × S) :
    sum (productChar ψ φ) a b = sum ψ a.1 b.1 * sum φ a.2 b.2 := by
  let : DecidableEq (R × S) := Classical.decEq _
  let e : (R × S)ˣ ≃ Rˣ × Sˣ :=
    { toFun := fun u => (Units.map (RingHom.fst R S).toMonoidHom u,
        Units.map (RingHom.snd R S).toMonoidHom u)
      invFun := fun u => ⟨((u.1 : R),(u.2 : S)), ((↑u.1⁻¹ : R),(↑u.2⁻¹ : S)),
        by ext <;> simp, by ext <;> simp⟩
      left_inv := fun u => by apply Units.ext; rfl
      right_inv := fun u => by apply Prod.ext <;> apply Units.ext <;> rfl }
  have h := Equiv.sum_comp e.symm
    (fun u : (R × S)ˣ => productChar ψ φ (a * (u : R × S) + b * (↑u⁻¹ : R × S)))
  calc
    _ = ∑ u : Rˣ, ∑ v : Sˣ,
        ψ (a.1 * (u : R) + b.1 * (↑u⁻¹ : R)) *
          φ (a.2 * (v : S) + b.2 * (↑v⁻¹ : S)) := by
      simpa [sum, Fintype.sum_prod_type, productChar, e] using! h.symm
    _ = _ := by
      simp only [sum, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

theorem sum_product_ringEquiv {T R S : Type*}
    [CommRing T] [CommRing R] [CommRing S] [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (a b : T) :
    sum ((productChar ψ φ).compAddMonoidHom e.toAddMonoidHom) a b =
      sum ψ (e a).1 (e b).1 * sum φ (e a).2 (e b).2 := by
  rw [sum_ringEquiv, sum_product]

end ErdosKloosterman

end

section

namespace ErdosKloosterman.PrimePower

variable {R : Type*} [CommRing R]

private theorem shift_mul_inverse (u : Rˣ) (t : R) (ht : t^2 = 0) :
    ((u : R) + t) * ((↑u⁻¹ : R) - t * (↑u⁻¹ : R)^2) = 1 := by
  calc
    _ = (u : R) * ↑u⁻¹ + t * ↑u⁻¹ * (1 - (u : R) * ↑u⁻¹) -
        t^2 * (↑u⁻¹ : R)^2 := by ring
    _ = 1 := by simp [ht]

def shiftUnit (u : Rˣ) (t : R) (ht : t^2 = 0) : Rˣ :=
  Units.mkOfMulEqOne ((u : R) + t) ((↑u⁻¹ : R) - t * (↑u⁻¹ : R)^2)
    (shift_mul_inverse u t ht)

@[simp] theorem shiftUnit_val (u : Rˣ) (t : R) (ht : t^2 = 0) :
    (shiftUnit u t ht : R) = (u : R) + t := rfl

@[simp] theorem shiftUnit_inv_val (u : Rˣ) (t : R) (ht : t^2 = 0) :
    (↑(shiftUnit u t ht)⁻¹ : R) = (↑u⁻¹ : R) - t * (↑u⁻¹ : R)^2 := rfl

def shiftEquiv (t : R) (ht : t^2 = 0) : Rˣ ≃ Rˣ where
  toFun u := shiftUnit u t ht
  invFun u := shiftUnit u (-t) (by simpa using ht)
  left_inv u := by apply Units.ext; simp
  right_inv u := by apply Units.ext; simp

theorem phase_shift (a b : R) (u : Rˣ) (t : R) (ht : t^2 = 0) :
    a * (shiftUnit u t ht : R) + b * (↑(shiftUnit u t ht)⁻¹ : R) =
      a * (u : R) + b * (↑u⁻¹ : R) + t * (a - b * (↑u⁻¹ : R)^2) := by
  rw [shiftUnit_val, shiftUnit_inv_val]
  ring

end ErdosKloosterman.PrimePower

end

section

open scoped BigOperators

namespace ErdosKloosterman

variable {F : Type*} [Field F]

theorem pair_eq_or_swap {u v z w : F}
    (hs : u + v = z + w) (hp : u * v = z * w) :
    (u = z ∧ v = w) ∨ (u = w ∧ v = z) := by
  have h : (u - z) * (u - w) = 0 := by
    linear_combination u * hs - hp
  rcases mul_eq_zero.mp h with h | h
  · left
    have hu := sub_eq_zero.mp h
    exact ⟨hu, by rw [hu] at hs; exact add_left_cancel hs⟩
  · right
    have hu := sub_eq_zero.mp h
    exact ⟨hu, by rw [hu, add_comm z w] at hs; exact add_left_cancel hs⟩

theorem inverse_pair_collision (u v z w : Fˣ)
    (hs : (u : F) + v = z + w)
    (hi : (↑u⁻¹ : F) + ↑v⁻¹ = ↑z⁻¹ + ↑w⁻¹) :
    ((u : F) + v = 0 ∧ (z : F) + w = 0) ∨
      (u = z ∧ v = w) ∨ (u = w ∧ v = z) := by
  by_cases hz : (u : F) + v = 0
  · exact Or.inl ⟨hz, hs.symm.trans hz⟩
  right
  have hid : (u : F)⁻¹ + (v : F)⁻¹ = (z : F)⁻¹ + (w : F)⁻¹ := by
    simpa only [Units.val_inv_eq_inv_val] using hi
  have hp : (u : F) * v = z * w := by
    have hzero : ((u : F) + v) * ((z : F) * w - (u : F) * v) = 0 := by
      field_simp at hid
      linear_combination hid - ((u : F) * v) * hs
    have hd := (mul_eq_zero.mp hzero).resolve_left hz
    exact (sub_eq_zero.mp hd).symm
  rcases pair_eq_or_swap hs hp with ⟨huz, hvw⟩ | ⟨huw, hvz⟩
  · exact Or.inl ⟨Units.ext huz, Units.ext hvw⟩
  · exact Or.inr ⟨Units.ext huw, Units.ext hvz⟩

end ErdosKloosterman

end

section

open scoped BigOperators
namespace ErdosHyperbolaIdentities

attribute [local instance] Classical.decEq

private theorem card_mul_fibre {A B : Type*} [Group A] [Fintype A]
    [Group B] [Fintype B] (f : A →* B) (hf : Function.Surjective f) (b : B) :
    Fintype.card B * ((Finset.univ : Finset A).filter fun x => f x = b).card =
      Fintype.card A := by
  calc
    _ = ∑ _y : B, ((Finset.univ : Finset A).filter fun x => f x = b).card := by simp
    _ = ∑ y : B, ((Finset.univ : Finset A).filter fun x => f x = y).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf y)
    _ = _ := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp

theorem unitClass_card_mul_totient (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) : T.totient * (unitClass N T hT a).card = N.totient := by
  let f : (ZMod N)ˣ →* (ZMod T)ˣ := ZMod.unitsMap hT
  have hf : Function.Surjective f := ZMod.unitsMap_surjective hT
  have hc := card_mul_fibre f hf a
  simpa only [unitClass, f, ZMod.card_units_eq_totient] using hc

theorem restrictedSum_zero (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) :
    restrictedSum N T hT a c 0 0 = (unitClass N T hT a).card := by
  simp [restrictedSum]

theorem restrictedSum_zero_eq_totient_ratio (N T : ℕ) [NeZero N] [NeZero T] (hT : T ∣ N)
    (a : (ZMod T)ˣ) (c : (ZMod N)ˣ) :
    restrictedSum N T hT a c 0 0 = (N.totient : ℂ)/(T.totient : ℂ) := by
  have hphi : (T.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos T)).ne'
  rw [restrictedSum_zero]
  apply (eq_div_iff hphi).mpr
  have hc := unitClass_card_mul_totient N T hT a
  have hcomplex : (T.totient : ℂ) * ((unitClass N T hT a).card : ℂ) = N.totient := by
    exact_mod_cast hc
  simpa only [mul_comm] using hcomplex

end ErdosHyperbolaIdentities

end

section

open scoped BigOperators

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable (F : Type*) [Field F] [Fintype F]

noncomputable def pairCollisions : Finset ((Fˣ × Fˣ) × (Fˣ × Fˣ)) :=
  Finset.univ.filter fun x =>
    (x.1.1 : F) + x.1.2 = x.2.1 + x.2.2 ∧
      (↑x.1.1⁻¹ : F) + ↑x.1.2⁻¹ = ↑x.2.1⁻¹ + ↑x.2.2⁻¹

theorem pairCollisions_card_le :
    (pairCollisions F).card ≤ 3 * (Fintype.card Fˣ) ^ 2 := by
  let zeroFamily := (Finset.univ : Finset (Fˣ × Fˣ)).image
    (fun p => ((p.1, -p.1), (p.2, -p.2)))
  let diagonalFamily := (Finset.univ : Finset (Fˣ × Fˣ)).image (fun p => (p, p))
  let swappedFamily := (Finset.univ : Finset (Fˣ × Fˣ)).image
    (fun p => (p, (p.2, p.1)))
  have cover : pairCollisions F ⊆ zeroFamily ∪ diagonalFamily ∪ swappedFamily := by
    rintro ⟨⟨u,v⟩,⟨z,w⟩⟩ hx
    obtain ⟨hs, hi⟩ := (Finset.mem_filter.mp hx).2
    rcases inverse_pair_collision u v z w hs hi with hz | hd | he
    · have hv : v = -u := by
        apply Units.ext
        change (v : F) = -(u : F)
        linear_combination hz.1
      have hw : w = -z := by
        apply Units.ext
        change (w : F) = -(z : F)
        linear_combination hz.2
      subst v; subst w
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨(u,z), Finset.mem_univ _, rfl⟩))
    · rcases hd with ⟨huz, hvw⟩
      subst z; subst w
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(u,v), Finset.mem_univ _, rfl⟩))
    · rcases he with ⟨huw, hvz⟩
      subst w; subst z
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(u,v), Finset.mem_univ _, rfl⟩)
  have hz : zeroFamily.card ≤ (Fintype.card Fˣ)^2 := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fˣ × Fˣ)))
        (f := fun p : Fˣ × Fˣ => ((p.1, -p.1), (p.2, -p.2))))
  have hd : diagonalFamily.card ≤ (Fintype.card Fˣ)^2 := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fˣ × Fˣ)))
        (f := fun p : Fˣ × Fˣ => (p,p)))
  have hs : swappedFamily.card ≤ (Fintype.card Fˣ)^2 := by
    simpa only [Finset.card_univ, Fintype.card_prod, pow_two] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fˣ × Fˣ)))
        (f := fun p : Fˣ × Fˣ => (p,(p.2,p.1))))
  have h1 := Finset.card_union_le zeroFamily diagonalFamily
  have h2 := Finset.card_union_le (zeroFamily ∪ diagonalFamily) swappedFamily
  have h3 := Finset.card_le_card cover
  omega

end ErdosKloosterman

end

end Erdos970

end OAI
