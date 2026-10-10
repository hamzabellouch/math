import Mathlib
import OAI.Computability.QuantumFactoring.LevelIndependence
import OAI.Computability.QuantumFactoring.PrimePowerLevels

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

abbrev Component (m : ℕ) := {p : ℕ // p ∈ m.primeFactors}

instance componentNeZero (m : ℕ) (p : Component m) :
    NeZero (p.val ^ m.factorization p.val) :=
  ⟨pow_ne_zero _ (Nat.mem_primeFactors.mp p.property).1.ne_zero⟩

abbrev ComponentUnits (m : ℕ) (p : Component m) :=
  (ZMod (p.val ^ m.factorization p.val))ˣ

noncomputable def unitCRT (m : ℕ) (hm : m ≠ 0) :
    (ZMod m)ˣ ≃* (∀ p : Component m, ComponentUnits m p) :=
  (Units.mapEquiv (ZMod.equivPi m hm).toMulEquiv).trans MulEquiv.piUnits

lemma component_order_level_lt {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (a : ComponentUnits m p) : padicValNat 2 (orderOf a) < n := by
  have ho : 0 < orderOf a := orderOf_pos a
  have hpow : 2^padicValNat 2 (orderOf a) ≤ orderOf a := Nat.le_of_dvd ho pow_padicValNat_dvd
  have hcard : Nat.card (ComponentUnits m p) = (p.val ^ m.factorization p.val).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
  calc
    _ ≤ orderOf a := hpow
    _ ≤ Nat.card (ComponentUnits m p) := orderOf_le_card
    _ = _ := hcard
    _ ≤ p.val ^ m.factorization p.val := Nat.totient_le _
    _ ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.ordProj_dvd _ _)
    _ < 2^n := hmn

noncomputable def componentLevel {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (a : ComponentUnits m p) : Fin (n+1) :=
  ⟨padicValNat 2 (orderOf a), by have := component_order_level_lt hm hmn p a; omega⟩

lemma componentLevel_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p : Component m) (t : Fin (n+1)) :
    Fintype.card {a : ComponentUnits m p // componentLevel hm hmn p a = t} =
      primePowerLevelCard p.val (m.factorization p.val) t.val := by
  classical
  rw [primePowerLevelCard, Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun a => Fin.ext_iff)

/-- Closed form for the number of favorable unit residues. Only n+1 levels
and the prime-power factors occur; there is no modulo-m residue enumeration. -/
def favorableCount (m n : ℕ) : ℕ :=
  m.totient - ∑ t : Fin (n+1), ∏ p : Component m,
    closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val

noncomputable def FavorableUnit {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (p₀ : Component m) (a : (ZMod m)ˣ) : Prop :=
  ¬ ∀ p, componentLevel hm hmn p (unitCRT m hm a p) =
    componentLevel hm hmn p₀ (unitCRT m hm a p₀)

lemma equal_component_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    Fintype.card {a : ∀ p : Component m, ComponentUnits m p //
      ∀ p, componentLevel hm hmn p (a p) = componentLevel hm hmn p₀ (a p₀)} =
    ∑ t : Fin (n+1), ∏ p : Component m,
      closedLevelCount (primePowerUnitCount p.val (m.factorization p.val)) t.val := by
  classical
  rw [allEqualLevel_card p₀]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro p hp
  rw [componentLevel_card]
  have pp := Nat.mem_primeFactors.mp p.property
  exact primePowerLevelCard_eq pp.1 (by
    intro h
    apply (Nat.not_even_iff_odd.mpr hodd)
    exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
    (pp.1.factorization_pos_of_dvd hm pp.2.1) _

/-- The exact source F is the cardinality of the actual CRT favorable event. -/
theorem favorableCount_eq_card {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ : Component m) :
    favorableCount m n = Nat.card {a : (ZMod m)ˣ // FavorableUnit hm hmn p₀ a} := by
  classical
  let : NeZero m := ⟨hm⟩
  rw [Nat.card_eq_fintype_card]
  unfold FavorableUnit
  rw [Fintype.card_subtype_compl, ZMod.card_units_eq_totient]
  unfold favorableCount
  congr 1
  rw [← equal_component_card hm hmn hodd p₀]
  exact (Fintype.card_congr ((unitCRT m hm).toEquiv.subtypeEquiv (fun _ => Iff.rfl))).symm

/-- At least half the units are favorable whenever there are two distinct
odd prime-power components, exactly as in Section 5. -/
theorem totient_le_twice_favorableCount {m n : ℕ} (hm : m ≠ 0) (hmn : m < 2^n)
    (hodd : Odd m) (p₀ p₁ : Component m) (hne : p₁ ≠ p₀) :
    m.totient ≤ 2 * favorableCount m n := by
  classical
  let : NeZero m := ⟨hm⟩
  have hhalf := twice_allEqualLevel_card_le p₀ p₁ hne (componentLevel hm hmn) (by
    intro t
    rw [componentLevel_card]
    have pp := Nat.mem_primeFactors.mp p₀.property
    have hpp := primePowerLevelCard_half pp.1 (by
      intro h
      apply (Nat.not_even_iff_odd.mpr hodd)
      exact even_iff_two_dvd.mpr (h ▸ pp.2.1))
      (pp.1.factorization_pos_of_dvd hm pp.2.1) t.val
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow pp.1
      (pp.1.factorization_pos_of_dvd hm pp.2.1)]
    simpa only [primePowerUnitCount, mul_comm] using hpp)
  rw [equal_component_card hm hmn hodd p₀] at hhalf
  have hc : Fintype.card (∀ p : Component m, ComponentUnits m p) = m.totient := by
    rw [← Fintype.card_congr (unitCRT m hm).toEquiv, ZMod.card_units_eq_totient]
  rw [hc] at hhalf
  unfold favorableCount
  omega

end ExactQuantumFactoring


end

end OAI
