import OAI.MathematicalPhysics.Heisenberg.NetworkEnergy

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module

open scoped Classical

namespace Heisenberg.Flow

abbrev Orthant (k : ℕ) := Fin (k + 1) → ℕ

def level {k : ℕ} (n : Orthant k) : ℕ := ∑ j, n j

def layerMass (k N : ℕ) : ℝ := ((N + k).choose k : ℝ)⁻¹

lemma layerMass_pos (k N : ℕ) : 0 < layerMass k N := by
  apply inv_pos.mpr
  exact_mod_cast Nat.choose_pos (by omega : k ≤ N + k)

lemma layerMass_zero (k : ℕ) : layerMass k 0 = 1 := by simp [layerMass]

lemma layerMass_recurrence (k N : ℕ) :
    layerMass k N * (N + 1) / (N + k + 1) = layerMass k (N + 1) := by
  have hc : (0 : ℝ) < (N + k).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ N + k)
  have hc' : (0 : ℝ) < (N + 1 + k).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ N + 1 + k)
  have he := Nat.choose_mul_succ_eq (N + k) k
  rw [show N + k + 1 - k = N + 1 by omega,
    show N + k + 1 = N + 1 + k by omega] at he
  have he' : ((N + k).choose k : ℝ) * (N + k + 1) =
      ((N + 1 + k).choose k : ℝ) * (N + 1) := by
    exact_mod_cast (by simpa [Nat.add_right_comm] using he)
  dsimp [layerMass]
  field_simp
  nlinarith [he']

def orthantFlow {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) : ℝ :=
  layerMass k (level n) * (n j + 1) / (level n + k + 1)

lemma flow_nonneg {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) :
    0 ≤ orthantFlow n j := by
  unfold orthantFlow
  exact div_nonneg (mul_nonneg (layerMass_pos _ _).le (by positivity)) (by positivity)

lemma coord_le_level {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) : n j ≤ level n :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

lemma outgoing {k : ℕ} (n : Orthant k) :
    ∑ j, orthantFlow n j = layerMass k (level n) := by
  have hs : (∑ j : Fin (k + 1), ((n j : ℝ) + 1)) = (level n : ℝ) + k + 1 := by
    simp [Finset.sum_add_distrib, level, Nat.cast_sum, add_assoc]
  simp only [orthantFlow, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hs]
  exact mul_div_cancel_right₀ _ (by positivity)

def predecessor {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) : Orthant k :=
  Function.update n j (n j - 1)

lemma predecessor_level {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) (hj : 0 < n j) :
    level (predecessor n j) + 1 = level n := by
  have hp : predecessor n j j + 1 = n j := by simp [predecessor]; omega
  have he : ∑ i ∈ Finset.univ.erase j, predecessor n j i =
      ∑ i ∈ Finset.univ.erase j, n i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [predecessor, (Finset.mem_erase.mp hi).1]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin (k + 1)))
    (predecessor n j) (Finset.mem_univ j)
  have hsum' := Finset.sum_erase_add (Finset.univ : Finset (Fin (k + 1)))
    n (Finset.mem_univ j)
  dsimp [level]
  omega

lemma level_zero_iff {k : ℕ} (n : Orthant k) : level n = 0 ↔ n = 0 := by
  constructor
  · intro h
    funext j
    have := coord_le_level n j
    simp only [Pi.zero_apply]
    omega
  · rintro rfl; simp [level]

lemma incoming {k : ℕ} (n : Orthant k) (hn : n ≠ 0) :
    ∑ j, (if 0 < n j then orthantFlow (predecessor n j) j else 0) =
      layerMass k (level n) := by
  have hN : 0 < level n := Nat.pos_of_ne_zero (mt (level_zero_iff n).mp hn)
  obtain ⟨N, hlev⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have heach (j : Fin (k + 1)) :
      (if 0 < n j then orthantFlow (predecessor n j) j else 0) =
        layerMass k N * (n j : ℝ) / (N + k + 1) := by
    split_ifs with hj
    · have hp := predecessor_level n j hj
      have hp' : level (predecessor n j) = N := by omega
      have hj' : ((n j - 1 : ℕ) : ℝ) + 1 = n j := by exact_mod_cast Nat.sub_add_cancel hj
      rw [orthantFlow, hp']
      simp only [predecessor, Function.update_self]
      rw [hj']
    · have hj' : n j = 0 := by omega
      simp [hj']
  simp_rw [heach]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
  change layerMass k N * (level n : ℝ) / _ = _
  rw [hlev]
  push_cast
  exact layerMass_recurrence k N

theorem orthant_divergence {k : ℕ} (n : Orthant k) :
    (∑ j, orthantFlow n j) -
      (∑ j, if 0 < n j then orthantFlow (predecessor n j) j else 0) =
        if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [outgoing, level, layerMass_zero]
  · rw [outgoing, incoming n hn, sub_self, ite_eq_right hn]

lemma flow_le_layerMass {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) :
    orthantFlow n j ≤ layerMass k (level n) := by
  unfold orthantFlow
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < level n + k + 1)).mpr
  apply mul_le_mul_of_nonneg_left _ (layerMass_pos _ _).le
  have hc : (n j : ℝ) ≤ level n := by exact_mod_cast coord_le_level n j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  linarith

lemma layerMass_decay (k N : ℕ) :
    layerMass k N ≤ (k.factorial : ℝ) / (N + 1) ^ k := by
  have hprod := Nat.pow_succ_le_ascFactorial (N + 1) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at hprod
  have hprod' : (N + 1 : ℝ) ^ k ≤ (k.factorial : ℝ) * (N + k).choose k := by
    exact_mod_cast hprod
  have hc : (0 : ℝ) < (N + k).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ N + k)
  have hn : (0 : ℝ) < (N + 1) ^ k := by positivity
  rw [layerMass, inv_eq_one_div, div_le_div_iff₀ hc hn]
  simpa using hprod'

theorem orthant_flow_envelope {k : ℕ} (n : Orthant k) (j : Fin (k + 1))
    (h : ℕ) (hh : h ≤ level n) :
    |orthantFlow n j| ≤ (k.factorial : ℝ) / (h + 1) ^ k := by
  rw [abs_of_nonneg (flow_nonneg n j)]
  apply (flow_le_layerMass n j).trans
  apply (layerMass_decay k (level n)).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

abbrev ZSite (k : ℕ) := Fin (k + 1) → ℤ

def PositiveOrthant {k : ℕ} (x : ZSite k) : Prop := ∀ j, 0 ≤ x j

def natPart {k : ℕ} (x : ZSite k) : Orthant k := fun j => (x j).toNat

def down {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) : ZSite k :=
  Function.update x j (x j - 1)

def latticeFlow {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) : ℝ :=
  if PositiveOrthant x then orthantFlow (natPart x) j else 0

lemma down_positive {k : ℕ} (x : ZSite k) (j : Fin (k + 1))
    (hx : PositiveOrthant x) : PositiveOrthant (down x j) ↔ 0 < x j := by
  constructor
  · intro hp
    have := hp j
    simp only [down, Function.update_self] at this
    omega
  · intro hj i
    by_cases hi : i = j
    · subst i; simp only [down, Function.update_self]; omega
    · simpa [down, hi] using hx i

lemma positive_of_down {k : ℕ} (x : ZSite k) (j : Fin (k + 1))
    (hx : PositiveOrthant (down x j)) : PositiveOrthant x := by
  intro i
  by_cases hi : i = j
  · subst i
    have := hx j
    simp only [down, Function.update_self] at this
    omega
  · have := hx i
    simpa [down, hi] using this

lemma natPart_down {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) :
    natPart (down x j) = predecessor (natPart x) j := by
  funext i
  by_cases hi : i = j
  · subst i
    simp only [natPart, down, predecessor, Function.update_self]
    omega
  · simp [natPart, down, predecessor, hi]

lemma natPart_zero_iff {k : ℕ} (x : ZSite k) (hx : PositiveOrthant x) :
    natPart x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    have := hx j
    simp only [natPart, Pi.zero_apply] at hj ⊢
    omega
  · rintro rfl; funext j; rfl

lemma lattice_incoming_formula {k : ℕ} (x : ZSite k) (hx : PositiveOrthant x)
    (j : Fin (k + 1)) :
    latticeFlow (down x j) j =
      if 0 < natPart x j then orthantFlow (predecessor (natPart x) j) j else 0 := by
  have hc : 0 < natPart x j ↔ 0 < x j := by simp [natPart]
  by_cases hj : 0 < x j
  · rw [latticeFlow, ite_eq_left ((down_positive x j hx).mpr hj),
      natPart_down, ite_eq_left (hc.mpr hj)]
  · rw [latticeFlow, ite_eq_right (mt (down_positive x j hx).mp hj),
      ite_eq_right (mt hc.mp hj)]

theorem lattice_divergence {k : ℕ} (x : ZSite k) :
    (∑ j, latticeFlow x j) - (∑ j, latticeFlow (down x j) j) =
      if x = 0 then 1 else 0 := by
  by_cases hx : PositiveOrthant x
  · simp only [latticeFlow, ite_eq_left hx]
    change (∑ j, orthantFlow (natPart x) j) -
      (∑ j, latticeFlow (down x j) j) = _
    simp_rw [lattice_incoming_formula x hx]
    simp only [orthant_divergence, natPart_zero_iff x hx]
  · have hn : x ≠ 0 := by rintro rfl; exact hx (by intro j; simp)
    have hp (j : Fin (k + 1)) : ¬PositiveOrthant (down x j) :=
      mt (positive_of_down x j) hx
    simp only [latticeFlow, ite_eq_right hx, ite_eq_right (hp _), Finset.sum_const_zero,
      sub_zero, ite_eq_right hn]

def radius {k : ℕ} (x : ZSite k) : ℕ := Finset.univ.sup (fun j => (x j).natAbs)

lemma radius_le_level {k : ℕ} (x : ZSite k) (hx : PositiveOrthant x) :
    radius x ≤ level (natPart x) := by
  apply Finset.sup_le
  intro j _
  have he : (x j).natAbs = (x j).toNat := by
    have ha := Int.natAbs_of_nonneg (hx j)
    have hb := Int.toNat_of_nonneg (hx j)
    omega
  rw [he]
  exact coord_le_level (natPart x) j

theorem lattice_flow_envelope {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) :
    |latticeFlow x j| ≤ (k.factorial : ℝ) / (radius x + 1) ^ k := by
  by_cases hx : PositiveOrthant x
  · rw [latticeFlow, ite_eq_left hx]
    exact orthant_flow_envelope (natPart x) j _ (radius_le_level x hx)
  · rw [latticeFlow, ite_eq_right hx, abs_zero]
    positivity

end Heisenberg.Flow

end

end OAI
