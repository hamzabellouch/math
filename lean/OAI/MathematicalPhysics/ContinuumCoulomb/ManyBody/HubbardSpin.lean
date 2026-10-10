import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardOccupation
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHamiltonian
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

namespace OAI

/-! Identifying the singly occupied exterior sector with the spin model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def wedgeModes (n : ℕ) (v : Fin n → Fin (Q + 1)) : Space Q :=
  ExteriorAlgebra.ιMulti ℂ n (fun k => mode (v k))

theorem wedgeModes_succ (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1)) :
    wedgeModes (n + 1) v = create (v 0) (wedgeModes n (fun k => v k.succ)) := by
  simp [wedgeModes, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, create, Function.comp_def]

theorem wedgeModes_replace_zero (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1))
    (i : Fin (Q + 1)) :
    wedgeModes (n + 1) (fun a => if a = 0 then i else v a) =
      create i (wedgeModes n (fun a => v a.succ)) := by
  simp [wedgeModes_succ]

theorem wedgeModes_replace_succ (n : ℕ) (v : Fin (n + 1) → Fin (Q + 1))
    (i : Fin (Q + 1)) (k : Fin n) :
    wedgeModes (n + 1) (fun a => if a = k.succ then i else v a) =
      create (v 0) (wedgeModes n (fun a => if a = k then i else v a.succ)) := by
  have h : (0 : Fin (n + 1)) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
  simp [wedgeModes_succ, h]

/-- Even fermion bilinears pass a spectator creator without a sign. -/
theorem transfer_create (i j k : Fin (Q + 1)) :
    transfer i j * create k =
      delta j k • create i + create k * transfer i j := by
  have hc := eq_neg_of_add_eq_zero_left (create_anticommute i k)
  calc
    _ = create i * (annihilate j * create k) := by rw [transfer, mul_assoc]
    _ = delta j k • create i - (create i * create k) * annihilate j := by
      rw [annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one, mul_assoc]
    _ = _ := by rw [hc]; ext x; simp [transfer]

/-- The action of a bilinear on an arbitrary wedge is the sum of its
one-particle replacements, with all CAR signs derived. -/
theorem transfer_wedgeModes (i j : Fin (Q + 1)) (n : ℕ)
    (v : Fin n → Fin (Q + 1)) :
    transfer i j (wedgeModes n v) =
      ∑ k, delta j (v k) • wedgeModes n (fun a => if a = k then i else v a) := by
  induction n with
  | zero => simp [wedgeModes, transfer, annihilate]
  | succ n ih =>
    rw [wedgeModes_succ]
    have h := LinearMap.congr_fun (transfer_create i j (v 0))
      (wedgeModes n (fun k => v k.succ))
    change transfer i j (create (v 0) (wedgeModes n (fun k => v k.succ))) =
      delta j (v 0) • create i (wedgeModes n (fun k => v k.succ)) +
        create (v 0) (transfer i j (wedgeModes n (fun k => v k.succ))) at h
    rw [h, ih, map_sum, Fin.sum_univ_succ, wedgeModes_replace_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, wedgeModes_replace_succ]

def siteModes (m : ℕ) : Fin (m + 1) × Fin 2 ≃ Fin ((2 * m + 1) + 1) :=
  finProdFinEquiv.trans (Fin.castOrderIso (by omega)).toEquiv

def siteMode (m : ℕ) (i : Fin (m + 1)) (σ : Fin 2) : Fin ((2 * m + 1) + 1) :=
  siteModes m (i, σ)

theorem siteMode_eq_iff (m : ℕ) (i j : Fin (m + 1)) (σ τ : Fin 2) :
    siteMode m i σ = siteMode m j τ ↔ i = j ∧ σ = τ := by
  rw [siteMode, siteMode, Equiv.apply_eq_iff_eq]
  exact Prod.mk_inj

theorem siteMode_ne_of_ne (m : ℕ) (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ : Fin 2) :
    siteMode m i σ ≠ siteMode m j τ :=
  fun h => hij ((siteMode_eq_iff m i j σ τ).mp h).1

def spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2) : Space (2 * m + 1) :=
  wedgeModes (m + 1) (fun i => siteMode m i (s i))

/-- Local spin flips act with coefficient one on the ordered wedge;
spectator parities cancel because the operator is an even bilinear. -/
theorem transfer_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i : Fin (m + 1)) (σ τ : Fin 2) :
    transfer (siteMode m i σ) (siteMode m i τ) (spinWedge m s) =
      if s i = τ then spinWedge m (Function.update s i σ) else 0 := by
  unfold spinWedge
  rw [transfer_wedgeModes]
  by_cases his : s i = τ
  · simp only [his, ↓reduceIte]
    rw [Finset.sum_eq_single i]
    · have hδ : delta (siteMode m i τ) (siteMode m i (s i)) = 1 := by
        simp [delta, his]
      rw [hδ, one_smul]
      congr 1
      funext a
      by_cases ha : a = i
      · subst a
        simp
      · simp [ha]
    · intro k _ hki
      have hne : siteMode m i τ ≠ siteMode m k (s k) := by
        intro h
        exact hki ((siteMode_eq_iff m i k τ (s k)).mp h).1.symm
      simp [delta, hne]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · simp only [his, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    have hne : siteMode m i τ ≠ siteMode m k (s k) := by
      intro h
      obtain ⟨hik, hτ⟩ := (siteMode_eq_iff m i k τ (s k)).mp h
      subst k
      exact his hτ.symm
    simp [delta, hne]

theorem sourceSpinSwap_eq_updates (m : ℕ) (s : SourceSpinBasis (m + 1))
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    sourceSpinSwap i j s = Function.update (Function.update s j (s i)) i (s j) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [sourceSpinSwap_apply]
  · by_cases hkj : k = j
    · subst k
      simp [sourceSpinSwap_apply, Ne.symm hij]
    · simp [sourceSpinSwap_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

theorem number_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i : Fin (m + 1)) (σ : Fin 2) :
    number (siteMode m i σ) (spinWedge m s) =
      if s i = σ then spinWedge m s else 0 := by
  rw [number, transfer_spinWedge]
  by_cases h : s i = σ
  · rw [← h, Function.update_eq_self]
  · simp [h]

theorem local_number_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i : Fin (m + 1)) :
    (number (siteMode m i 0) + number (siteMode m i 1)) (spinWedge m s) = spinWedge m s := by
  simp only [LinearMap.add_apply, number_spinWedge]
  have h : s i = 0 ∨ s i = 1 := by omega
  rcases h with h | h <;> simp [h]

theorem transfers_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) (σ τ ρ υ : Fin 2) :
    (transfer (siteMode m i σ) (siteMode m i τ) *
        transfer (siteMode m j ρ) (siteMode m j υ)) (spinWedge m s) =
      if s i = τ ∧ s j = υ then
        spinWedge m (Function.update (Function.update s j ρ) i σ) else 0 := by
  rw [Module.End.mul_apply, transfer_spinWedge]
  by_cases hj : s j = υ
  · simp only [hj, ↓reduceIte]
    rw [transfer_spinWedge]
    simp [hij]
  · simp [hj]

theorem spinSwap_eq_sum (m : ℕ) (i j : Fin (m + 1)) (hij : i ≠ j) :
    spinSwap (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1) =
      ∑ σ : Fin 2, ∑ τ : Fin 2,
        transfer (siteMode m i σ) (siteMode m i τ) *
          transfer (siteMode m j τ) (siteMode m j σ) := by
  have hc := (transfer_commute_of_distinct (siteMode m j 0) (siteMode m j 1)
    (siteMode m i 1) (siteMode m i 0)
    (siteMode_ne_of_ne m j i (Ne.symm hij) 1 1)
    (siteMode_ne_of_ne m i j hij 0 0)).eq
  simp only [Fin.sum_univ_two, spinSwap, number]
  rw [hc]
  abel

/-- The fermionic exchange is exactly the source coordinate swap,
including its sign and every spectator spin. -/
theorem spinSwap_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    spinSwap (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
        (spinWedge m s) = spinWedge m (sourceSpinSwap i j s) := by
  rw [spinSwap_eq_sum m i j hij]
  simp only [LinearMap.sum_apply]
  simp_rw [transfers_spinWedge m s i j hij]
  rw [Finset.sum_eq_single (s j)]
  · rw [Finset.sum_eq_single (s i)]
    · simp only [and_self, ↓reduceIte]
      rw [← sourceSpinSwap_eq_updates m s i j hij]
    · intro τ _ hτ
      simp [Ne.symm hτ]
    · intro hi
      exact (hi (Finset.mem_univ (s i))).elim
  · intro σ _ hσ
    apply Finset.sum_eq_zero
    intro τ _
    simp [Ne.symm hσ]
  · intro hj
    exact (hj (Finset.mem_univ (s j))).elim

theorem siteHeisenberg_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    siteHeisenberg (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
        (spinWedge m s) =
      (2 : ℂ) • spinWedge m (sourceSpinSwap i j s) - spinWedge m s := by
  simp only [siteHeisenberg, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, spinSwap_spinWedge m s i j hij]

/-- The genuine many-mode hopping square gives the Heisenberg
superexchange numerator on every spin configuration. -/
theorem twoSiteHopping_sq_spinWedge (m : ℕ) (s : Fin (m + 1) → Fin 2)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    (twoSiteHopping (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1) *
      twoSiteHopping (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1))
        (spinWedge m s) =
      (2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap i j s)) := by
  have hab : siteMode m i 0 ≠ siteMode m i 1 := by
    intro h
    have hs := (siteMode_eq_iff m i i 0 1).mp h
    norm_num at hs
  have hcd : siteMode m j 0 ≠ siteMode m j 1 := by
    intro h
    have hs := (siteMode_eq_iff m j j 0 1).mp h
    norm_num at hs
  have h := twoSiteHopping_sq_on_singlyOccupied
    (siteMode m i 0) (siteMode m i 1) (siteMode m j 0) (siteMode m j 1)
    hab (siteMode_ne_of_ne m i j hij 0 0) (siteMode_ne_of_ne m i j hij 0 1)
    (siteMode_ne_of_ne m i j hij 1 0) (siteMode_ne_of_ne m i j hij 1 1) hcd
    (spinWedge m s) (local_number_spinWedge m s i) (local_number_spinWedge m s j)
  rw [LinearMap.sub_apply, Module.End.one_apply, siteHeisenberg_spinWedge m s i j hij] at h
  rw [h]
  simp only [two_smul]
  abel

end ContinuumCoulomb.HubbardGlobal

end

end OAI
