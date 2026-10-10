import OAI.Analysis.Laughlin.Operators.NormalOrder
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

namespace OAI

/-!
# Global finite-fermion identities for the Hubbard reduction

These are identities of actual creation and contraction operators on
the finite exterior algebra.  They retain every spectator mode and
therefore do not assume transition signs from the two-site calculation.
-/

noncomputable section

namespace ContinuumCoulomb.HubbardGlobal

open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def transfer (i j : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  create i * annihilate j

def number (i : Fin (Q + 1)) : Module.End ℂ (Space Q) := transfer i i

def totalNumber (Q : ℕ) : Module.End ℂ (Space Q) := ∑ i, number i

theorem transfer_mul (i j k l : Fin (Q + 1)) :
    transfer i j * transfer k l = delta j k • transfer i l -
      create i * create k * annihilate j * annihilate l := by
  simpa only [transfer, one_mul, mul_one] using
    normal_order_entry (1 : Module.End ℂ (Space Q)) 1 j i k l

theorem quartic_exchange (i j k l : Fin (Q + 1)) :
    create i * create k * annihilate j * annihilate l =
      create k * create i * annihilate l * annihilate j := by
  have hc := eq_neg_of_add_eq_zero_left (create_anticommute i k)
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute j l)
  calc
    _ = (create i * create k) * (annihilate j * annihilate l) := by noncomm_ring
    _ = (-(create k * create i)) * (-(annihilate l * annihilate j)) := by rw [hc, ha]
    _ = _ := by ext x; simp

/-- The matrix-unit commutator, proved from the full CAR operators. -/
theorem transfer_commutator (i j k l : Fin (Q + 1)) :
    transfer i j * transfer k l - transfer k l * transfer i j =
      delta j k • transfer i l - delta l i • transfer k j := by
  rw [transfer_mul, transfer_mul, quartic_exchange i j k l]
  abel

theorem number_idempotent (i : Fin (Q + 1)) : number i * number i = number i := by
  unfold number
  rw [transfer_mul]
  simp [delta, create_sq]

theorem number_commute (i j : Fin (Q + 1)) : Commute (number i) (number j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply sub_eq_zero.mp
    simpa [number, delta, hij, Ne.symm hij] using transfer_commutator i i j j

theorem number_transfer_commutator (i j k : Fin (Q + 1)) :
    number i * transfer j k - transfer j k * number i =
      (delta i j - delta i k) • transfer j k := by
  have h := transfer_commutator i i j k
  by_cases hij : i = j <;> by_cases hik : i = k <;>
    simp_all [number, delta, eq_comm]
  ext x
  simp

theorem annihilate_number_self (i : Fin (Q + 1)) :
    annihilate i * number i = annihilate i := by
  calc
    _ = (annihilate i * create i) * annihilate i := rfl
    _ = (1 - create i * annihilate i) * annihilate i := by
      rw [annihilate_create]
      simp [delta]
    _ = _ := by simp [sub_mul, mul_assoc, annihilate_sq]

theorem annihilate_number_commute (i j : Fin (Q + 1)) (hij : i ≠ j) :
    Commute (annihilate i) (number j) := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute i j)
  calc
    annihilate i * number j = (annihilate i * create j) * annihilate j := rfl
    _ = -(create j * annihilate i) * annihilate j := by
      rw [annihilate_create]
      simp [delta, hij]
    _ = -(create j * (annihilate i * annihilate j)) := by ext x; simp
    _ = number j * annihilate i := by rw [ha]; ext x; simp [number, transfer]

theorem pair_annihilate_siteNumber (i j : Fin (Q + 1)) (hij : i ≠ j) :
    (annihilate i * annihilate j) * (number i + number j) =
      (2 : ℂ) • (annihilate i * annihilate j) := by
  have hleft : (annihilate i * annihilate j) * number i =
      annihilate i * annihilate j := by
    calc
      _ = annihilate i * (annihilate j * number i) := by rw [mul_assoc]
      _ = annihilate i * (number i * annihilate j) := by
        rw [(annihilate_number_commute j i (Ne.symm hij)).eq]
      _ = (annihilate i * number i) * annihilate j := by rw [mul_assoc]
      _ = _ := by rw [annihilate_number_self]
  have hright : (annihilate i * annihilate j) * number j =
      annihilate i * annihilate j := by rw [mul_assoc, annihilate_number_self]
  rw [mul_add, hleft, hright, two_smul]

/-- Local particle number one rules out a pair annihilation, directly
from the CAR; no occupation-basis or sign assumption is needed. -/
theorem pair_annihilate_of_single (i j : Fin (Q + 1)) (hij : i ≠ j)
    (x : Space Q) (hx : (number i + number j) x = x) :
    (annihilate i * annihilate j) x = 0 := by
  have h := LinearMap.congr_fun (pair_annihilate_siteNumber i j hij) x
  change (annihilate i * annihilate j) ((number i + number j) x) =
    (2 : ℂ) • ((annihilate i * annihilate j) x) at h
  rw [hx] at h
  exact add_left_cancel (show
    (annihilate i * annihilate j) x + (annihilate i * annihilate j) x =
      (annihilate i * annihilate j) x + 0 by simpa only [two_smul, add_zero] using h.symm)

theorem transfer_commute_of_distinct (i j k l : Fin (Q + 1))
    (hjk : j ≠ k) (hli : l ≠ i) : Commute (transfer i j) (transfer k l) := by
  apply sub_eq_zero.mp
  simpa [delta, hjk, hli] using transfer_commutator i j k l

theorem transfer_sq_of_ne (i j : Fin (Q + 1)) (hij : i ≠ j) :
    transfer i j * transfer i j = 0 := by
  rw [transfer_mul]
  simp [delta, Ne.symm hij, create_sq]

theorem quartic_number (i j : Fin (Q + 1)) (hij : i ≠ j) :
    create i * create j * annihilate j * annihilate i = number i * number j := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute i j)
  calc
    _ = -((create i * create j) * (annihilate i * annihilate j)) := by
      rw [ha]
      ext x
      simp
    _ = _ := by
      rw [number, number, transfer_mul]
      simp only [delta, ite_eq_right hij, zero_smul, zero_sub]
      noncomm_ring

theorem transfer_reverse_product (i j : Fin (Q + 1)) (hij : i ≠ j) :
    transfer i j * transfer j i = number i - number i * number j := by
  rw [transfer_mul, quartic_number i j hij]
  simp [delta, number]

def bondTransfer (i j : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  transfer i j + transfer j i

theorem bondTransfer_sq (i j : Fin (Q + 1)) (hij : i ≠ j) :
    bondTransfer i j * bondTransfer i j =
      number i + number j - (2 : ℂ) • (number i * number j) := by
  have hn := (number_commute i j).eq
  unfold bondTransfer
  rw [add_mul, mul_add, mul_add, transfer_sq_of_ne i j hij,
    transfer_sq_of_ne j i (Ne.symm hij), transfer_reverse_product i j hij,
    transfer_reverse_product j i (Ne.symm hij), ← hn]
  simp only [zero_add, add_zero, two_smul]
  abel

/-- A two-transfer exchange identity before imposing occupation
constraints.  It is independent of every spectator mode. -/
theorem transfer_exchange (i j k l : Fin (Q + 1))
    (hjk : j ≠ k) (hlk : l ≠ k) :
    transfer i j * transfer k l = -(transfer i l * transfer k j) := by
  have ha := eq_neg_of_add_eq_zero_left (annihilate_anticommute j l)
  rw [transfer_mul, transfer_mul]
  simp only [delta, ite_eq_right hjk, ite_eq_right hlk, zero_smul, zero_sub, neg_neg]
  calc
    _ = -(create i * create k * (annihilate j * annihilate l)) := by noncomm_ring
    _ = _ := by rw [ha]; ext x; simp

theorem bondTransfer_commute (a b c d : Fin (Q + 1))
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) :
    Commute (bondTransfer a c) (bondTransfer b d) := by
  exact ((transfer_commute_of_distinct a c b d hcb (Ne.symm had)).add_right
      (transfer_commute_of_distinct a c d b hcd (Ne.symm hab))).add_left
    ((transfer_commute_of_distinct c a b d hab (Ne.symm hcd)).add_right
      (transfer_commute_of_distinct c a d b had (Ne.symm hcb)))

def spinSwap (a b c d : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  number a * number c + number b * number d +
    transfer a b * transfer d c + transfer c d * transfer b a

def twoSiteHopping (a b c d : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  bondTransfer a c + bondTransfer b d

/-- The full hopping-square identity.  The final two terms are the
pair hops, which vanish on singly occupied sites. -/
theorem twoSiteHopping_sq (a b c d : Fin (Q + 1))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    twoSiteHopping a b c d * twoSiteHopping a b c d =
      number a + number b + number c + number d - (2 : ℂ) • spinSwap a b c d -
        (2 : ℂ) • (create a * create b * annihilate c * annihilate d +
          create c * create d * annihilate a * annihilate b) := by
  have hcomm := (bondTransfer_commute a b c d hab had (Ne.symm hbc) hcd).eq
  have hacbd : transfer a c * transfer b d =
      -(create a * create b * annihilate c * annihilate d) := by
    rw [transfer_mul]
    simp [delta, Ne.symm hbc]
  have hcadb : transfer c a * transfer d b =
      -(create c * create d * annihilate a * annihilate b) := by
    rw [transfer_mul]
    simp [delta, had]
  have hacdb := transfer_exchange a c d b hcd hbd
  have hcabd := transfer_exchange c a b d hab (Ne.symm hbd)
  unfold twoSiteHopping
  rw [add_mul, mul_add, mul_add, bondTransfer_sq a c hac, bondTransfer_sq b d hbd,
    ← hcomm]
  unfold bondTransfer
  rw [add_mul, mul_add, mul_add, hacbd, hcadb, hacdb, hcabd]
  unfold spinSwap
  simp only [two_smul]
  abel

def siteHeisenberg (a b c d : Fin (Q + 1)) : Module.End ℂ (Space Q) :=
  (2 : ℂ) • spinSwap a b c d - 1

/-- The occupied-sector second-order numerator, on a genuine Fock
vector with arbitrary spectators and local particle number one. -/
theorem twoSiteHopping_sq_on_singlyOccupied (a b c d : Fin (Q + 1))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : Space Q)
    (hleft : (number a + number b) x = x)
    (hright : (number c + number d) x = x) :
    (twoSiteHopping a b c d * twoSiteHopping a b c d) x =
      (1 - siteHeisenberg a b c d) x := by
  have hpairLeft := pair_annihilate_of_single a b hab x hleft
  have hpairRight := pair_annihilate_of_single c d hcd x hright
  have hQl : (create a * create b * annihilate c * annihilate d) x = 0 := by
    change (create a * create b) ((annihilate c * annihilate d) x) = 0
    rw [hpairRight, map_zero]
  have hQr : (create c * create d * annihilate a * annihilate b) x = 0 := by
    change (create c * create d) ((annihilate a * annihilate b) x) = 0
    rw [hpairLeft, map_zero]
  have htotal : (number a + number b + number c + number d) x = (2 : ℂ) • x := by
    change number a x + number b x = x at hleft
    change number c x + number d x = x at hright
    change number a x + number b x + number c x + number d x = (2 : ℂ) • x
    rw [two_smul]
    rw [add_assoc (number a x + number b x), hleft, hright]
  rw [twoSiteHopping_sq a b c d hab hac had hbc hbd hcd]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [htotal]
  simp only [LinearMap.add_apply, hQl, hQr, add_zero, smul_zero, sub_zero,
    siteHeisenberg, LinearMap.sub_apply, Module.End.one_apply, two_smul]
  abel

/-- Every one-particle transfer preserves the total fermion number. -/
theorem totalNumber_commute_transfer (i j : Fin (Q + 1)) :
    Commute (totalNumber Q) (transfer i j) := by
  apply sub_eq_zero.mp
  unfold totalNumber
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [number_transfer_commutator]
  rw [← Finset.sum_smul]
  simp [delta, Finset.sum_sub_distrib]

def oneBody (w : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, w i j • transfer i j

def densityInteraction (v : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, v i j • (number i * number j)

theorem totalNumber_commute_oneBody (w : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    Commute (totalNumber Q) (oneBody w) := by
  unfold oneBody
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (totalNumber_commute_transfer i j).smul_right _

theorem totalNumber_commute_densityInteraction
    (v : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    Commute (totalNumber Q) (densityInteraction v) := by
  unfold densityInteraction
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((totalNumber_commute_transfer i i).mul_right
    (totalNumber_commute_transfer j j)).smul_right _

/-- The actual hopping-plus-density Hamiltonian preserves every fixed
particle-number sector, including the half-filled sector used here. -/
theorem preserves_number_sector (w v : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (x : Space Q) (N : ℂ) (hx : totalNumber Q x = N • x) :
    totalNumber Q ((oneBody w + densityInteraction v) x) =
      N • ((oneBody w + densityInteraction v) x) := by
  have hc := (totalNumber_commute_oneBody w).add_right
    (totalNumber_commute_densityInteraction v)
  have h := LinearMap.congr_fun hc.eq x
  change totalNumber Q ((oneBody w + densityInteraction v) x) =
    (oneBody w + densityInteraction v) (totalNumber Q x) at h
  rw [hx, map_smul] at h
  exact h

end ContinuumCoulomb.HubbardGlobal

end

end OAI
