import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PeriodicTilingThree.SharedSeed

abbrev Residues (p : ℕ) := ZMod (p ^ 2) × ZMod (p ^ 2)
abbrev ActiveLabels := ZMod 3 ⊕ (Fin 2 × ZMod 2)
abbrev InactiveLabels (m : ℕ) := Fin m × (ZMod 2 × ZMod 3)
abbrev LabelledResidue (m : ℕ) :=
  ZMod 3 ⊕ ((Fin 2 × ZMod 2) ⊕ InactiveLabels m)

def residue (p : ℕ) (x : ℤ × ℤ) : Residues p := (x.1, x.2)

def firstPoint (p : ℕ) (y : ZMod 3) : Residues p :=
  ((p * y.val : ℕ), 1)

def secondPoint (p : ℕ) (u : Fin 2 × ZMod 2) : Residues p :=
  ((p * (2 * u.1.val + u.2.val) : ℕ), 2)

def activePoint (p : ℕ) : ActiveLabels → Residues p :=
  Sum.elim (firstPoint p) (secondPoint p)

def firstRegion (p : ℕ) : Set (Residues p) := Set.range (firstPoint p)
def secondRegion (p : ℕ) : Set (Residues p) := Set.range (secondPoint p)
def Rest (p : ℕ) := {s : Residues p // s ∉ Set.range (activePoint p)}
def copyCount (p : ℕ) : ℕ := (p ^ 4 - 7) / 6

private theorem nat_multiple_cast_injective {p u v : ℕ}
    (hp : 0 < p) (hu : u < p) (hv : v < p)
    (h : (p * u : ZMod (p ^ 2)) = (p * v : ZMod (p ^ 2))) : u = v := by
  have hu' : p * u < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hu hp
  have hv' : p * v < p ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_left hv hp
  have hn : ((p * u : ℕ) : ZMod (p ^ 2)) = ((p * v : ℕ) : ZMod (p ^ 2)) := by
    simpa only [Nat.cast_mul] using h
  have hh := congrArg ZMod.val hn
  rw [ZMod.val_natCast_of_lt hu', ZMod.val_natCast_of_lt hv'] at hh
  exact Nat.eq_of_mul_eq_mul_left hp hh

theorem firstPoint_injective {p : ℕ} (hlarge : 200 < p) :
    Function.Injective (firstPoint p) := by
  intro y y' h
  apply ZMod.val_injective 3
  apply nat_multiple_cast_injective (by omega)
      (lt_trans (ZMod.val_lt y) (by omega : 3 < p))
      (lt_trans (ZMod.val_lt y') (by omega : 3 < p))
  simpa only [firstPoint, Nat.cast_mul] using congrArg Prod.fst h

theorem secondPoint_injective {p : ℕ} (hlarge : 200 < p) :
    Function.Injective (secondPoint p) := by
  rintro ⟨c,y⟩ ⟨c',y'⟩ h
  have hc := c.isLt
  have hc' := c'.isLt
  have hy := ZMod.val_lt y
  have hy' := ZMod.val_lt y'
  have hcode : 2 * c.val + y.val = 2 * c'.val + y'.val := by
    apply nat_multiple_cast_injective (p := p) (by omega) (by omega) (by omega)
    simpa only [secondPoint, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      using congrArg Prod.fst h
  have hcc : c.val = c'.val := by omega
  have hyy : y.val = y'.val := by omega
  exact Prod.ext (Fin.ext hcc) (ZMod.val_injective 2 hyy)

theorem firstPoint_ne_secondPoint {p : ℕ} (hlarge : 200 < p)
    (y : ZMod 3) (u : Fin 2 × ZMod 2) : firstPoint p y ≠ secondPoint p u := by
  intro h
  have hp2 : 2 < p ^ 2 := lt_of_lt_of_le (by norm_num : 2 < 201 ^ 2)
    (Nat.pow_le_pow_left (by omega : 201 ≤ p) 2)
  have hh := congrArg (fun s : Residues p => s.2.val) h
  change (1 : ZMod (p ^ 2)).val = (2 : ZMod (p ^ 2)).val at hh
  have h1 : (1 : ZMod (p ^ 2)).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p ^ 2)
  have h2 : (2 : ZMod (p ^ 2)).val = 2 := by
    simpa only [Nat.cast_ofNat] using ZMod.val_natCast_of_lt hp2
  have h12 : (1 : ℕ) = 2 := h1.symm.trans (hh.trans h2)
  omega

theorem activePoint_injective {p : ℕ} (hlarge : 200 < p) :
    Function.Injective (activePoint p) := by
  intro a b h
  cases a with
  | inl y =>
    cases b with
    | inl y' => exact congrArg Sum.inl (firstPoint_injective hlarge h)
    | inr u => exact (firstPoint_ne_secondPoint hlarge y u h).elim
  | inr u =>
    cases b with
    | inl y => exact (firstPoint_ne_secondPoint hlarge y u h.symm).elim
    | inr u' => exact congrArg Sum.inr (secondPoint_injective hlarge h)

theorem first_second_disjoint {p : ℕ} (hlarge : 200 < p) :
    Disjoint (firstRegion p) (secondRegion p) := by
  rw [Set.disjoint_left]
  rintro s ⟨y, rfl⟩ ⟨u, hu⟩
  exact firstPoint_ne_secondPoint hlarge y u hu.symm

theorem seven_le_pow {p : ℕ} (hlarge : 200 < p) : 7 ≤ p ^ 4 := by
  exact le_trans (by norm_num : 7 ≤ 201 ^ 4)
    (Nat.pow_le_pow_left (by omega : 201 ≤ p) 4)

theorem pow_four_mod_six {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    p ^ 4 % 6 = 1 := by
  have htwo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hthree : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    omega
  have hsix : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rw [Nat.pow_mod]
  rcases hsix with h | h <;> norm_num [h]

theorem six_dvd_remainder {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    6 ∣ p ^ 4 - 7 := by
  apply Nat.dvd_of_mod_eq_zero
  have hmod := pow_four_mod_six hp hlarge
  have hge := seven_le_pow hlarge
  omega

theorem copyCount_mul_six {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    copyCount p * 6 = p ^ 4 - 7 := by
  exact Nat.div_mul_cancel (six_dvd_remainder hp hlarge)

theorem six_mul_copyCount_add_seven {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) : 6 * copyCount p + 7 = p ^ 4 := by
  have h := copyCount_mul_six hp hlarge
  have hge := seven_le_pow hlarge
  omega

noncomputable def restEquiv {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    Rest p ≃ InactiveLabels (copyCount p) := by
  classical
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega)⟩
  letI : Fintype (Rest p) := by unfold Rest; infer_instance
  apply Fintype.equivOfCardEq
  have hactive : Fintype.card (Set.range (activePoint p)) = 7 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (activePoint_injective hlarge))]
    norm_num [ActiveLabels]
  have hrest : Fintype.card (Rest p) = p ^ 4 - 7 := by
    change Fintype.card ((Set.range (activePoint p))ᶜ : Set (Residues p)) = _
    rw [Fintype.card_compl_set, hactive]
    simp only [Residues, Fintype.card_prod, ZMod.card]
    congr 1
    ring
  rw [hrest]
  simpa [InactiveLabels, Fintype.card_prod, Nat.mul_assoc]
    using (copyCount_mul_six hp hlarge).symm

noncomputable def residueAssembly {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    LabelledResidue (copyCount p) ≃ Residues p := by
  classical
  exact (Equiv.sumAssoc (ZMod 3) (Fin 2 × ZMod 2)
      (InactiveLabels (copyCount p))).symm |>.trans
    ((Equiv.sumCongr (Equiv.ofInjective (activePoint p)
      (activePoint_injective hlarge)) (restEquiv hp hlarge).symm).trans
      (Equiv.Set.sumCompl (Set.range (activePoint p))))

noncomputable def residueEquiv {p : ℕ} (hp : p.Prime) (hlarge : 200 < p) :
    Residues p ≃ LabelledResidue (copyCount p) :=
  (residueAssembly hp hlarge).symm

@[simp] theorem residueAssembly_first {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (y : ZMod 3) :
    residueAssembly hp hlarge (Sum.inl y) = firstPoint p y := rfl

@[simp] theorem residueAssembly_second {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (u : Fin 2 × ZMod 2) :
    residueAssembly hp hlarge (Sum.inr (Sum.inl u)) = secondPoint p u := rfl

@[simp] theorem residueEquiv_firstPoint {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (y : ZMod 3) :
    residueEquiv hp hlarge (firstPoint p y) = Sum.inl y :=
  (residueAssembly hp hlarge).symm_apply_apply (Sum.inl y)

@[simp] theorem residueEquiv_secondPoint {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (u : Fin 2 × ZMod 2) :
    residueEquiv hp hlarge (secondPoint p u) = Sum.inr (Sum.inl u) :=
  (residueAssembly hp hlarge).symm_apply_apply (Sum.inr (Sum.inl u))

theorem residueEquiv_first_iff {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (s : Residues p) :
    (∃ y, residueEquiv hp hlarge s = Sum.inl y) ↔ s ∈ firstRegion p := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (residueEquiv hp hlarge).injective
    rw [residueEquiv_firstPoint, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨y, residueEquiv_firstPoint hp hlarge y⟩

theorem residueEquiv_second_iff {p : ℕ} (hp : p.Prime)
    (hlarge : 200 < p) (s : Residues p) :
    (∃ u, residueEquiv hp hlarge s = Sum.inr (Sum.inl u)) ↔
      s ∈ secondRegion p := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply (residueEquiv hp hlarge).injective
    rw [residueEquiv_secondPoint, hu]
  · rintro ⟨u, rfl⟩
    exact ⟨u, residueEquiv_secondPoint hp hlarge u⟩

def reduce (p : ℕ) (s : Residues p) : ZMod p × ZMod p :=
  let f := ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
  (f s.1, f s.2)

@[simp] theorem reduce_firstPoint (p : ℕ) (y : ZMod 3) :
    reduce p (firstPoint p y) = (0, 1) := by
  let f : ZMod (p ^ 2) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
  change (f ((p * y.val : ℕ) : ZMod (p ^ 2)), f 1) = (0, 1)
  apply Prod.ext
  · rw [map_natCast]
    simp [Nat.cast_mul]
  · exact map_one f

@[simp] theorem reduce_secondPoint (p : ℕ) (u : Fin 2 × ZMod 2) :
    reduce p (secondPoint p u) = (0, 2) := by
  let f : ZMod (p ^ 2) →+* ZMod p :=
    ZMod.castHom (show p ∣ p ^ 2 from ⟨p, by ring⟩) (ZMod p)
  change (f ((p * (2 * u.1.val + u.2.val) : ℕ) : ZMod (p ^ 2)), f 2) = (0, 2)
  apply Prod.ext
  · rw [map_natCast]
    simp [Nat.cast_mul]
  · simpa only [Nat.cast_ofNat] using map_natCast f 2

theorem reduce_of_firstRegion {p : ℕ} {s : Residues p}
    (hs : s ∈ firstRegion p) : reduce p s = (0, 1) := by
  obtain ⟨y, rfl⟩ := hs
  exact reduce_firstPoint p y

theorem reduce_of_secondRegion {p : ℕ} {s : Residues p}
    (hs : s ∈ secondRegion p) : reduce p s = (0, 2) := by
  obtain ⟨u, rfl⟩ := hs
  exact reduce_secondPoint p u

noncomputable def outputEquiv {p : ℕ} (hlarge : 200 < p) :
    Residues p ≃ ZMod (p ^ 4) := by
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (by omega)⟩
  letI : NeZero (p ^ 4) := ⟨pow_ne_zero 4 (by omega)⟩
  apply Fintype.equivOfCardEq
  simp only [Residues, Fintype.card_prod, ZMod.card]
  ring

end PeriodicTilingThree.SharedSeed

end OAI
