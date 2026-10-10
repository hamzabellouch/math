import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResourceMoments

namespace OAI

/-!
# Cardinality budgets for the representation resource event

These inequalities turn the actual leaf-product counts and the valid-entry
encoding into the resource moments. The remaining input is the deterministic
integer allocation estimate for each leaf and entry envelope.
-/

namespace LowSpaceSubsetSum.RepresentationMoments

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem pow_two_add (x y : ℝ) : (2 : ℝ) ^ x * 2 ^ y = 2 ^ (x + y) :=
  (Real.rpow_add (by norm_num) _ _).symm


omit [Fintype ι] [DecidableEq ι] in
/-- Direct binomial counting of the prescribed top/local choices and arbitrary
background choices. This includes empty and full prescribed subsets. -/
theorem leaf_card_entropy (L : RepresentationLeaf ι)
    (ht : L.topCount ≤ L.top.card) (hl : L.localCount ≤ L.mixer.card) :
    (L.occurrences.card : ℝ) ≤ (2 : ℝ) ^
      ((L.top.card : ℝ) * binaryEntropy ((L.topCount : ℝ) / L.top.card) +
       (L.mixer.card : ℝ) * binaryEntropy ((L.localCount : ℝ) / L.mixer.card) + L.background.card) := by
  rw [L.occurrences_card, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have htop := (choose_entropy_bounds L.top.card L.topCount ht).2
  have hlocal := (choose_entropy_bounds L.mixer.card L.localCount hl).2
  calc
    _ ≤ ((2 : ℝ) ^ ((L.top.card : ℝ) * binaryEntropy ((L.topCount : ℝ) / L.top.card)) *
      (2 : ℝ) ^ ((L.mixer.card : ℝ) * binaryEntropy ((L.localCount : ℝ) / L.mixer.card))) *
        (2 : ℝ) ^ L.background.card := by gcongr
    _ = _ := by rw [pow_two_add, ← Real.rpow_natCast, pow_two_add]

private theorem entropy_power_cap {u E A : ℝ} (hu : 0 < u) (k : ℕ)
    (h : E ≤ A + Real.logb 2 (u ^ k)) :
    (2 : ℝ) ^ E ≤ u ^ k * (2 : ℝ) ^ A := by
  calc
    _ ≤ (2 : ℝ) ^ (A + Real.logb 2 (u ^ k)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    _ = _ := by
      rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      ring

omit [Fintype ι] [DecidableEq ι] in
/-- The allocation estimate supplies an entropy inequality; no leaf count is
assumed. The finite cardinality follows from direct combination counting. -/
theorem leaf_card_of_allocation (L : RepresentationLeaf ι)
    (ht : L.topCount ≤ L.top.card) (hl : L.localCount ≤ L.mixer.card)
    {u beta : ℝ} (hu : 0 < u)
    (hAllocation : (L.top.card : ℝ) * binaryEntropy ((L.topCount : ℝ) / L.top.card) +
       (L.mixer.card : ℝ) * binaryEntropy ((L.localCount : ℝ) / L.mixer.card) + L.background.card ≤
         beta / 2 + Real.logb 2 (u ^ 10)) :
    (L.occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (beta / 2) :=
  (leaf_card_entropy L ht hl).trans (entropy_power_cap hu 10 hAllocation)

omit [Fintype ι] [DecidableEq ι] in
theorem child_card_bound (L : Fin 4 → RepresentationLeaf ι) {u beta : ℝ}
    (_hu : 0 ≤ u)
    (hLeaf : ∀ i, ((L i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (beta / 2))
    (j : Fin 2) :
    ((RepresentationUniverse.children L j).card : ℝ) ≤ u ^ 20 * (2 : ℝ) ^ beta := by
  rw [RepresentationUniverse.children_card, Nat.cast_mul]
  have h := mul_le_mul (hLeaf ⟨2 * j.val, by omega⟩)
    (hLeaf ⟨2 * j.val + 1, by omega⟩) (by positivity)
    (by positivity : 0 ≤ u ^ 10 * (2 : ℝ) ^ (beta / 2))
  calc
    _ ≤ (u ^ 10 * (2 : ℝ) ^ (beta / 2)) * (u ^ 10 * (2 : ℝ) ^ (beta / 2)) := h
    _ = u ^ 20 * (2 : ℝ) ^ beta := by
      rw [mul_mul_mul_comm, ← pow_add, pow_two_add]
      congr 2; ring

omit [Fintype ι] [DecidableEq ι] in
theorem parent_card_bound (L : Fin 4 → RepresentationLeaf ι) {u beta : ℝ}
    (hu : 0 ≤ u)
    (hLeaf : ∀ i, ((L i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (beta / 2)) :
    ((RepresentationUniverse.parents L).card : ℝ) ≤ u ^ 40 * (2 : ℝ) ^ (2 * beta) := by
  rw [RepresentationUniverse.parents_card, Nat.cast_mul]
  have h := mul_le_mul (child_card_bound L hu hLeaf 0)
    (child_card_bound L hu hLeaf 1) (by positivity)
    (by positivity : 0 ≤ u ^ 20 * (2 : ℝ) ^ beta)
  calc
    _ ≤ (u ^ 20 * (2 : ℝ) ^ beta) * (u ^ 20 * (2 : ℝ) ^ beta) := h
    _ = u ^ 40 * (2 : ℝ) ^ (2 * beta) := by
      rw [mul_mul_mul_comm, ← pow_add, pow_two_add]
      congr 2; ring

/-- The five-power loss is exactly the proved lower bound for a nested modulus. -/
theorem divide_by_modulus {u N p beta ell : ℝ} (hu : 0 < u) (hp : 0 < p)
    (a : ℕ) (hN : N ≤ u ^ a * (2 : ℝ) ^ beta)
    (hmod : (2 : ℝ) ^ ell / u ^ 5 ≤ p) :
    N / p ≤ u ^ (a + 5) * (2 : ℝ) ^ (beta - ell) := by
  apply (div_le_iff₀ hp).mpr
  apply hN.trans
  have hmult := mul_le_mul_of_nonneg_left hmod
    (by positivity : 0 ≤ u ^ (a + 5) * (2 : ℝ) ^ (beta - ell))
  calc
    _ = (u ^ (a + 5) * (2 : ℝ) ^ (beta - ell)) * ((2 : ℝ) ^ ell / u ^ 5) := by
      rw [pow_add, Real.rpow_sub (by norm_num)]
      field_simp
    _ ≤ _ := hmult

/-- Two independent low filters incur two five-power modulus losses. -/
theorem divide_by_two_moduli {u N p q beta ell0 ell : ℝ}
    (hu : 0 < u) (hp : 0 < p) (hq : 0 < q) (a : ℕ)
    (hN : N ≤ u ^ a * (2 : ℝ) ^ beta)
    (hmod0 : (2 : ℝ) ^ ell0 / u ^ 5 ≤ p)
    (hmod : (2 : ℝ) ^ ell / u ^ 5 ≤ q) :
    N / (p * q) ≤ u ^ (a + 10) * (2 : ℝ) ^ (beta - ell0 - ell) := by
  have h1 := divide_by_modulus hu hp a hN hmod0
  have h2 := divide_by_modulus hu hq (a + 5) h1 hmod
  simpa only [Nat.add_assoc, Nat.reduceAdd, div_div] using h2

omit [Fintype ι] [DecidableEq ι] in
theorem pair_budget (L R : Fin 4 → RepresentationLeaf ι)
    {u betaL betaR ellL ellR pL pR gamma : ℝ} (hu : 4 ≤ u)
    (hpL : 0 < pL) (hpR : 0 < pR)
    (hL : ∀ i, ((L i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (betaL / 2))
    (hR : ∀ i, ((R i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (betaR / 2))
    (hmL : (2 : ℝ) ^ ellL / u ^ 5 ≤ pL) (hmR : (2 : ℝ) ^ ellR / u ^ 5 ≤ pR)
    (hgL : betaL - ellL ≤ gamma) (hgR : betaR - ellR ≤ gamma) :
    ((RepresentationUniverse.children L 0).card + (RepresentationUniverse.children L 1).card : ℝ) / pL +
      ((RepresentationUniverse.children R 0).card + (RepresentationUniverse.children R 1).card : ℝ) / pR ≤
        u ^ 26 * (2 : ℝ) ^ gamma := by
  have hu0 : 0 < u := by linarith
  have hl (j : Fin 2) := (divide_by_modulus hu0 hpL 20
    (child_card_bound L hu0.le hL j) hmL).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgL)
        (by positivity : 0 ≤ u ^ 25))
  have hr (j : Fin 2) := (divide_by_modulus hu0 hpR 20
    (child_card_bound R hu0.le hR j) hmR).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgR)
        (by positivity : 0 ≤ u ^ 25))
  rw [add_div, add_div]
  calc
    _ ≤ 4 * (u ^ 25 * (2 : ℝ) ^ gamma) := by linarith [hl 0, hl 1, hr 0, hr 1]
    _ ≤ u * (u ^ 25 * (2 : ℝ) ^ gamma) := mul_le_mul_of_nonneg_right hu (by positivity)
    _ = _ := by rw [show 26 = 25 + 1 by decide, pow_succ]; ring

omit [Fintype ι] [DecidableEq ι] in
theorem tuple_budget (L R : Fin 4 → RepresentationLeaf ι)
    {u betaL betaR ell0 ellL ellR p0 pL pR halfN : ℝ} (hu : 2 ≤ u)
    (hp0 : 0 < p0) (hpL : 0 < pL) (hpR : 0 < pR)
    (hL : ∀ i, ((L i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (betaL / 2))
    (hR : ∀ i, ((R i).occurrences.card : ℝ) ≤ u ^ 10 * (2 : ℝ) ^ (betaR / 2))
    (hm0 : (2 : ℝ) ^ ell0 / u ^ 5 ≤ p0)
    (hmL : (2 : ℝ) ^ ellL / u ^ 5 ≤ pL) (hmR : (2 : ℝ) ^ ellR / u ^ 5 ≤ pR)
    (hgL : 2 * betaL - ell0 - ellL ≤ halfN)
    (hgR : 2 * betaR - ell0 - ellR ≤ halfN) :
    ((RepresentationUniverse.parents L).card : ℝ) / (p0 * pL) +
      ((RepresentationUniverse.parents R).card : ℝ) / (p0 * pR) ≤
        u ^ 51 * (2 : ℝ) ^ halfN := by
  have hu0 : 0 < u := by linarith
  have hl := (divide_by_two_moduli hu0 hp0 hpL 40 (parent_card_bound L hu0.le hL) hm0 hmL).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgL)
      (by positivity : 0 ≤ u ^ 50))
  have hr := (divide_by_two_moduli hu0 hp0 hpR 40 (parent_card_bound R hu0.le hR) hm0 hmR).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hgR)
      (by positivity : 0 ≤ u ^ 50))
  calc
    _ ≤ 2 * (u ^ 50 * (2 : ℝ) ^ halfN) := by linarith
    _ ≤ u * (u ^ 50 * (2 : ℝ) ^ halfN) := mul_le_mul_of_nonneg_right hu (by positivity)
    _ = _ := by rw [show 51 = 50 + 1 by decide, pow_succ]; ring


/-- Exact entropy envelope for distinct valid entries. Local multiplicity is
removed by the distinct sumset before any low filter is considered. -/
theorem entry_card_entropy (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (ht : RepresentationUniverse.DisjointFour (L 0).top (L 1).top (L 2).top (L 3).top)
    (hk : (L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount ≤
      (RepresentationUniverse.topDomain L).card) :
    ((RepresentationUniverse.validEntries a L).card : ℝ) ≤ (2 : ℝ) ^
      ((RepresentationUniverse.topDomain L).card * binaryEntropy
        (((L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount : ℕ) /
          ((RepresentationUniverse.topDomain L).card : ℝ)) +
      (RepresentationUniverse.backgroundDomain L).card +
      ((RepresentationUniverse.mixerDomain L).card - deficiency a (RepresentationUniverse.mixerDomain L))) := by
  have hc : ((RepresentationUniverse.validEntries a L).card : ℝ) ≤
      (((RepresentationUniverse.topDomain L).card.choose ((L 0).topCount + (L 1).topCount +
        (L 2).topCount + (L 3).topCount) * 2 ^ (RepresentationUniverse.backgroundDomain L).card *
          distinctSumCount a (RepresentationUniverse.mixerDomain L) : ℕ) : ℝ) := by
    exact_mod_cast RepresentationUniverse.concrete_validEntries_card a L ht
  apply hc.trans
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ← two_pow_card_sub_deficiency]
  have htop := (choose_entropy_bounds _ _ hk).2
  calc
    _ ≤ ((2 : ℝ) ^ ((RepresentationUniverse.topDomain L).card * binaryEntropy
        (((L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount : ℕ) /
          ((RepresentationUniverse.topDomain L).card : ℝ))) *
      (2 : ℝ) ^ (RepresentationUniverse.backgroundDomain L).card) *
      (2 : ℝ) ^ ((RepresentationUniverse.mixerDomain L).card -
        deficiency a (RepresentationUniverse.mixerDomain L)) := by gcongr
    _ = _ := by rw [← Real.rpow_natCast, pow_two_add, pow_two_add]

/-- The entry moment follows from the allocation inequality and the actual
modulus lower bound, with exactly the paper's ten-power loss. -/
theorem entry_budget_of_allocation (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (ht : RepresentationUniverse.DisjointFour (L 0).top (L 1).top (L 2).top (L 3).top)
    (hk : (L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount ≤
      (RepresentationUniverse.topDomain L).card)
    {u ell0 p0 lambda : ℝ} (hu : 0 < u) (hp0 : 0 < p0)
    (hm0 : (2 : ℝ) ^ ell0 / u ^ 5 ≤ p0)
    (hAllocation : (RepresentationUniverse.topDomain L).card * binaryEntropy
        (((L 0).topCount + (L 1).topCount + (L 2).topCount + (L 3).topCount : ℕ) /
          ((RepresentationUniverse.topDomain L).card : ℝ)) +
      (RepresentationUniverse.backgroundDomain L).card +
      ((RepresentationUniverse.mixerDomain L).card - deficiency a (RepresentationUniverse.mixerDomain L)) ≤
        (lambda + ell0) + Real.logb 2 (u ^ 5)) :
    ((RepresentationUniverse.validEntries a L).card : ℝ) / p0 ≤ u ^ 10 * (2 : ℝ) ^ lambda := by
  have hcard := (entry_card_entropy a L ht hk).trans (entropy_power_cap hu 5 hAllocation)
  simpa only [Nat.reduceAdd, add_sub_cancel_right] using divide_by_modulus hu hp0 5 hcard hm0

/-- Entries are bounded through the actual finite envelope, before any residue
is exposed, rather than by an assumed filtered-entry expectation. -/
theorem entry_budget (a : ι → ℤ) (L : Fin 4 → RepresentationLeaf ι)
    (ht : RepresentationUniverse.DisjointFour (L 0).top (L 1).top (L 2).top (L 3).top)
    {u ell0 p0 lambda : ℝ} (hu : 0 < u) (hp0 : 0 < p0)
    (hm0 : (2 : ℝ) ^ ell0 / u ^ 5 ≤ p0)
    (hEnvelope :
      (((RepresentationUniverse.topDomain L).card.choose ((L 0).topCount + (L 1).topCount +
        (L 2).topCount + (L 3).topCount) * 2 ^ (RepresentationUniverse.backgroundDomain L).card *
          distinctSumCount a (RepresentationUniverse.mixerDomain L) : ℕ) : ℝ) ≤
            u ^ 5 * (2 : ℝ) ^ (lambda + ell0)) :
    ((RepresentationUniverse.validEntries a L).card : ℝ) / p0 ≤ u ^ 10 * (2 : ℝ) ^ lambda := by
  have hcard : ((RepresentationUniverse.validEntries a L).card : ℝ) ≤
      u ^ 5 * (2 : ℝ) ^ (lambda + ell0) :=
    le_trans (by exact_mod_cast RepresentationUniverse.concrete_validEntries_card a L ht) hEnvelope
  simpa only [Nat.reduceAdd, add_sub_cancel_right] using
    divide_by_modulus hu hp0 5 hcard hm0

end LowSpaceSubsetSum.RepresentationMoments

end OAI
