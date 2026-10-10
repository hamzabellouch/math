import Mathlib
import OAI.Computability.QuantumFactoring.FactorSplitting

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

/-- Dividing a positive multiple by a power of two preserves exactly the
order divisors with enough 2-adic slack. -/
theorem dvd_div_pow_two_iff {d r k : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) (hk : 2 ^ k ∣ r) :
    d ∣ r / 2 ^ k ↔ padicValNat 2 d + k ≤ padicValNat 2 r := by
  have hkle : k ≤ padicValNat 2 r := (padicValNat_dvd_iff_le hr).mp hk
  constructor
  · intro h
    have hquot : r / 2 ^ k ≠ 0 := by
      have : 2 ^ k ≤ r := Nat.le_of_dvd (Nat.pos_of_ne_zero hr) hk
      have : 0 < r / 2 ^ k := Nat.div_pos this (by positivity)
      omega
    have hh := level_le_of_dvd hquot h
    rw [padicValNat.div_pow hk] at hh
    omega
  · intro h
    rcases hdr with ⟨a, rfl⟩
    have hd : d ≠ 0 := left_ne_zero_of_mul hr
    have ha : a ≠ 0 := right_ne_zero_of_mul hr
    rw [padicValNat.mul hd ha] at h
    have hp : 2 ^ k ∣ a := (padicValNat_dvd_iff_le ha).mpr (by omega)
    apply (Nat.dvd_div_iff_mul_dvd hk).mpr
    simpa only [Nat.mul_comm (2 ^ k) d] using Nat.mul_dvd_mul_left d hp

/-- For a divisor, an exact valuation cutoff is a single ordinary divisibility
test; hence its size is a cyclic-group root count, not residue enumeration. -/
theorem level_le_iff_dvd_cutoff {d r t : ℕ} (hr : r ≠ 0) (hdr : d ∣ r) :
    padicValNat 2 d ≤ t ↔ d ∣ r / 2 ^ (padicValNat 2 r - t) := by
  have hle := level_le_of_dvd hr hdr
  have hp : 2 ^ (padicValNat 2 r - t) ∣ r :=
    (padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _)
  rw [dvd_div_pow_two_iff hr hdr hp]
  omega

noncomputable def cumulativeLevelCount (G : Type*) [Group G] [Fintype G] (t : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : G // padicValNat 2 (orderOf x) ≤ t}

noncomputable def levelCount (G : Type*) [Group G] [Fintype G] (t : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : G // padicValNat 2 (orderOf x) = t}

/-- The cumulative law of levels in every finite cyclic group. -/
theorem cumulativeLevelCount_eq (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    cumulativeLevelCount G t = Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) := by
  classical
  let r := Fintype.card G
  have hr : r ≠ 0 := Fintype.card_ne_zero
  let e := r / 2 ^ (padicValNat 2 r - t)
  have hediv : e ∣ r := Nat.div_dvd_of_dvd
    ((padicValNat_dvd_iff_le hr).mpr (Nat.sub_le _ _))
  have heq : ∀ x : G, padicValNat 2 (orderOf x) ≤ t ↔ x ∈ (powMonoidHom e : G →* G).ker := by
    intro x
    rw [level_le_iff_dvd_cutoff hr (show orderOf x ∣ r from orderOf_dvd_card)]
    exact orderOf_dvd_iff_pow_eq_one
  let E : {x : G // padicValNat 2 (orderOf x) ≤ t} ≃ (powMonoidHom e : G →* G).ker :=
    Equiv.subtypeEquivRight heq
  change Fintype.card _ = e
  rw [Fintype.card_congr E, ← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_ker]
  rw [Nat.card_eq_fintype_card]
  exact Nat.gcd_eq_right hediv

/-- Fibers are obtained by differencing two consecutive cumulative counts. -/
theorem levelCount_eq_cumulative (G : Type*) [Group G] [Fintype G] (t : ℕ) :
    levelCount G t = if t = 0 then cumulativeLevelCount G 0
      else cumulativeLevelCount G t - cumulativeLevelCount G (t - 1) := by
  classical
  by_cases ht : t = 0
  · subst t
    simp [levelCount, cumulativeLevelCount]
  · have hpartition : (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t)) =
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t)) ∪
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdis : Disjoint (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) = t))
        (Finset.univ.filter (fun x : G => padicValNat 2 (orderOf x) ≤ t - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      omega
    simp only [levelCount, cumulativeLevelCount, ht, ↓reduceIte, Fintype.card_subtype]
    rw [hpartition, Finset.card_union_of_disjoint hdis]
    omega

/-- Exact level counts use only cardinal arithmetic, powers of two and division. -/
theorem levelCount_cyclic (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] (t : ℕ) :
    levelCount G t = if t = 0 then
      Fintype.card G / 2 ^ padicValNat 2 (Fintype.card G)
    else Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - t) -
      Fintype.card G / 2 ^ (padicValNat 2 (Fintype.card G) - (t - 1)) := by
  rw [levelCount_eq_cumulative]
  simp only [cumulativeLevelCount_eq, Nat.sub_zero]

end ExactQuantumFactoring


end

end OAI
