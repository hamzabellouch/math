import OAI.Combinatorics.CompleteCrossing.Residues
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

namespace OAI

/-! Cyclic gap enumeration and the exact Harary–Hill crossing-tuple count. -/

section

noncomputable section
open scoped BigOperators
namespace Paper170

def naturalCrossingTuples (n : ℕ) : Finset (Fin 4 → ℕ) :=
  (crossingTuples n).image (fun v i => (v i).val)

theorem mem_naturalCrossingTuples {n : ℕ} {v : Fin 4 → ℕ} :
    v ∈ naturalCrossingTuples n ↔
      v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧ v 3 < n ∧
        residueColor n (v 0 + v 2) = residueColor n (v 1 + v 3) := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨_, hw, hc⟩ := Finset.mem_filter.mp hw
    exact ⟨hw (by decide : (0 : Fin 4) < 1), hw (by decide : (1 : Fin 4) < 2),
      hw (by decide : (2 : Fin 4) < 3), (w 3).isLt, hc⟩
  · rintro ⟨h₀, h₁, h₂, h₃, hc⟩
    have hb (i : Fin 4) : v i < n := by fin_cases i <;> dsimp <;> omega
    let w : Fin 4 → Fin n := fun i => ⟨v i, hb i⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hc⟩, rfl⟩
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simp only [w, Fin.mk_lt_mk] <;> assumption

theorem naturalCrossingTuples_card (n : ℕ) :
    (naturalCrossingTuples n).card = (crossingTuples n).card := by
  apply Finset.card_image_of_injective
  intro v w h
  funext i
  exact Fin.ext (congrFun h i)

abbrev CyclicRecord := Σ _ : ℕ, ℕ × ℕ × ℕ

def cyclicRecords (n : ℕ) : Finset CyclicRecord :=
  (Finset.Icc 2 (n - 2)).sigma (fun k => sameColorGapTuples n k)

theorem mem_cyclicRecords {n k a g h : ℕ} :
    (⟨k, a, g, h⟩ : CyclicRecord) ∈ cyclicRecords n ↔
      2 ≤ k ∧ k ≤ n - 2 ∧ a < n ∧ 1 ≤ g ∧ g ≤ k - 1 ∧
        1 ≤ h ∧ h ≤ n - k - 1 ∧
          residueColor n (2 * a + g + h) = residueColor n (2 * a + g + h + k) := by
  simp [cyclicRecords, sameColorGapTuples, and_assoc]

def cyclicToOrdered (n : ℕ) (p : CyclicRecord) : Fin 4 × (Fin 4 → ℕ) :=
  let k := p.1
  let a := p.2.1
  let b := a + p.2.2.1
  let c := b + p.2.2.2
  let d := a + k + p.2.2.2
  if d < n then (0, ![a, b, c, d])
  else if c < n then (1, ![d - n, a, b, c])
  else if b < n then (2, ![c - n, d - n, a, b])
  else (3, ![b - n, c - n, d - n, a])

def orderedToCyclic (n : ℕ) (q : Fin 4 × (Fin 4 → ℕ)) : CyclicRecord :=
  let v := q.2
  match q.1.val with
  | 0 => ⟨(v 1 - v 0) + (v 3 - v 2), v 0, v 1 - v 0, v 2 - v 1⟩
  | 1 => ⟨(v 2 - v 1) + (v 0 + n - v 3), v 1, v 2 - v 1, v 3 - v 2⟩
  | 2 => ⟨(v 3 - v 2) + (v 1 - v 0), v 2, v 3 - v 2, v 0 + n - v 3⟩
  | _ => ⟨(v 0 + n - v 3) + (v 2 - v 1), v 3, v 0 + n - v 3, v 1 - v 0⟩

theorem residueColor_shift_eq {n x y : ℕ} (t : ℕ) (h : x + t * n = y) :
    residueColor n x = residueColor n y := by
  rw [← h]
  simp [residueColor, Nat.add_mod]

theorem cyclicToOrdered_spec {n k a g h : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n - 2)
    (ha : a < n) (hg : 1 ≤ g) (hgk : g ≤ k - 1)
    (hh : 1 ≤ h) (hhn : h ≤ n - k - 1) :
    let v := (cyclicToOrdered n ⟨k, a, g, h⟩).2
    v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧ v 3 < n ∧
      (residueColor n (v 0 + v 2) = residueColor n (v 1 + v 3) ↔
        residueColor n (2 * a + g + h) = residueColor n (2 * a + g + h + k)) := by
  by_cases hd : a + k + h < n
  · simp only [cyclicToOrdered, hd, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
    rw [show a + (a + g + h) = 2 * a + g + h by omega,
      show a + g + (a + k + h) = 2 * a + g + h + k by omega]
  · by_cases hc : a + g + h < n
    · simp only [cyclicToOrdered, hd, hc, ↓reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
      rw [residueColor_shift_eq 1 (show (a + k + h - n + (a + g)) + 1 * n =
        2 * a + g + h + k by omega)]
      have he : a + (a + g + h) = 2 * a + g + h := by omega
      rw [he, eq_comm]
    · by_cases hb : a + g < n
      · simp only [cyclicToOrdered, hd, hc, hb, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        refine ⟨by omega, by omega, by omega, by trivial, ?_⟩
        rw [residueColor_shift_eq 1 (show (a + g + h - n + a) + 1 * n =
          2 * a + g + h by omega),
          residueColor_shift_eq 1 (show (a + k + h - n + (a + g)) + 1 * n =
          2 * a + g + h + k by omega)]
      · simp only [cyclicToOrdered, hd, hc, hb, ↓reduceIte, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
        refine ⟨by omega, by omega, by omega, ha, ?_⟩
        rw [residueColor_shift_eq 2 (show (a + g - n + (a + k + h - n)) + 2 * n =
          2 * a + g + h + k by omega),
          residueColor_shift_eq 1 (show (a + g + h - n + a) + 1 * n =
          2 * a + g + h by omega), eq_comm]

theorem orderedToCyclic_bounds {n : ℕ} (j : Fin 4) (v : Fin 4 → ℕ)
    (h₀ : v 0 < v 1) (h₁ : v 1 < v 2) (h₂ : v 2 < v 3) (h₃ : v 3 < n) :
    let p := orderedToCyclic n (j, v)
    2 ≤ p.1 ∧ p.1 ≤ n - 2 ∧ p.2.1 < n ∧ 1 ≤ p.2.2.1 ∧
      p.2.2.1 ≤ p.1 - 1 ∧ 1 ≤ p.2.2.2 ∧ p.2.2.2 ≤ n - p.1 - 1 := by
  fin_cases j <;> simp [orderedToCyclic] <;> omega

theorem orderedToCyclic_inverse {n : ℕ} (j : Fin 4) (v : Fin 4 → ℕ)
    (h₀ : v 0 < v 1) (h₁ : v 1 < v 2) (h₂ : v 2 < v 3) (h₃ : v 3 < n) :
    cyclicToOrdered n (orderedToCyclic n (j, v)) = (j, v) := by
  fin_cases j <;> simp (disch := omega) [orderedToCyclic, cyclicToOrdered]
  all_goals split_ifs <;> try omega
  all_goals
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> simp <;> omega

theorem cyclicToOrdered_inverse {n k a g h : ℕ} (hk : 2 ≤ k) (_hkn : k ≤ n - 2)
    (ha : a < n) (hg : 1 ≤ g) (hgk : g ≤ k - 1)
    (hh : 1 ≤ h) (hhn : h ≤ n - k - 1) :
    orderedToCyclic n (cyclicToOrdered n ⟨k, a, g, h⟩) = ⟨k, a, g, h⟩ := by
  unfold cyclicToOrdered
  dsimp only
  split_ifs <;> simp [orderedToCyclic] <;> omega

theorem cyclicToOrdered_mem {n : ℕ} {p : CyclicRecord} (hp : p ∈ cyclicRecords n) :
    cyclicToOrdered n p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n := by
  rcases p with ⟨k, a, g, h⟩
  obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn, hc⟩ := mem_cyclicRecords.mp hp
  obtain ⟨h₀, h₁, h₂, h₃, he⟩ := cyclicToOrdered_spec hk hkn ha hg hgk hh hhn
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
    mem_naturalCrossingTuples.mpr ⟨h₀, h₁, h₂, h₃, he.mpr hc⟩⟩

theorem orderedToCyclic_mem {n : ℕ} {q : Fin 4 × (Fin 4 → ℕ)}
    (hq : q ∈ (Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n) :
    orderedToCyclic n q ∈ cyclicRecords n := by
  rcases q with ⟨j, v⟩
  obtain ⟨h₀, h₁, h₂, h₃, hc⟩ := mem_naturalCrossingTuples.mp (Finset.mem_product.mp hq).2
  obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn⟩ := orderedToCyclic_bounds j v h₀ h₁ h₂ h₃
  apply mem_cyclicRecords.mpr
  refine ⟨hk, hkn, ha, hg, hgk, hh, hhn, ?_⟩
  have he := (cyclicToOrdered_spec hk hkn ha hg hgk hh hhn).2.2.2.2
  rw [show (⟨(orderedToCyclic n (j, v)).1, (orderedToCyclic n (j, v)).2.1,
      (orderedToCyclic n (j, v)).2.2.1, (orderedToCyclic n (j, v)).2.2.2⟩ : CyclicRecord) =
      orderedToCyclic n (j, v) from rfl, orderedToCyclic_inverse j v h₀ h₁ h₂ h₃] at he
  exact he.mp hc

theorem crossingTuples_cyclic_count {n : ℕ} (_hn : 3 ≤ n) :
    4 * (crossingTuples n).card =
      ∑ k ∈ Finset.Icc 2 (n - 2), (sameColorGapTuples n k).card := by
  have hcard : (cyclicRecords n).card =
      ((Finset.univ : Finset (Fin 4)) ×ˢ naturalCrossingTuples n).card := by
    apply Finset.card_nbij' (cyclicToOrdered n) (orderedToCyclic n)
    · exact fun _ hp => cyclicToOrdered_mem hp
    · exact fun _ hq => orderedToCyclic_mem hq
    · rintro ⟨k, a, g, h⟩ hp
      obtain ⟨hk, hkn, ha, hg, hgk, hh, hhn, _⟩ := mem_cyclicRecords.mp hp
      exact cyclicToOrdered_inverse hk hkn ha hg hgk hh hhn
    · rintro ⟨j, v⟩ hq
      obtain ⟨h₀, h₁, h₂, h₃, _⟩ := mem_naturalCrossingTuples.mp (Finset.mem_product.mp hq).2
      exact orderedToCyclic_inverse j v h₀ h₁ h₂ h₃
  simpa only [cyclicRecords, Finset.card_sigma, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, naturalCrossingTuples_card] using hcard.symm

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

def startingLabels (n k b : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a =>
    residueColor n (2 * a + b) = residueColor n (2 * a + b + k))

theorem startingLabels_card_eq_sum {n : ℕ} (hn : 0 < n) (k b : ℕ) :
    (startingLabels n k b).card =
      ∑ r ∈ sameColorResidues n k, (residueFiber n b r).card := by
  unfold residueFiber
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext a
  simp [startingLabels, sameColorResidues, residueColor,
    Nat.mod_lt _ hn, Nat.add_mod]

theorem startingLabels_card_odd {n : ℕ} (hn : Odd n) (k b : ℕ) :
    (startingLabels n k b).card = (sameColorResidues n k).card := by
  have hpos : 0 < n := by obtain ⟨t, ht⟩ := hn; omega
  rw [startingLabels_card_eq_sum hpos]
  calc
    (∑ r ∈ sameColorResidues n k, (residueFiber n b r).card) =
        ∑ _r ∈ sameColorResidues n k, 1 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueFiber_card_odd hn (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = _ := by simp

theorem startingLabels_card_even {m : ℕ} (hm : 0 < m) (k b : ℕ) :
    (startingLabels (2 * m) k b).card = 2 * (sameColorResiduesParity (2 * m) k (b % 2)).card := by
  rw [startingLabels_card_eq_sum (by omega)]
  calc
    (∑ r ∈ sameColorResidues (2 * m) k, (residueFiber (2 * m) b r).card) =
        ∑ r ∈ sameColorResidues (2 * m) k, if r % 2 = b % 2 then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueFiber_card_even hm (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    _ = _ := by rw [← Finset.sum_filter]; simp [sameColorResiduesParity, mul_comm]

theorem parity_partition (s : Finset ℕ) (b : ℕ) :
    (s.filter (fun r => (r + b) % 2 = 0)).card +
      (s.filter (fun r => (r + b) % 2 = 1)).card = s.card := by
  have he : s.filter (fun r => ¬(r + b) % 2 = 0) = s.filter (fun r => (r + b) % 2 = 1) := by
    ext r
    rcases Nat.mod_two_eq_zero_or_one (r + b) with h | h <;> simp [h]
  rw [← he]
  exact Finset.card_filter_add_card_filter_not (s := s) _

theorem startingLabels_card_even_balanced {m k : ℕ} (hm : 0 < m)
    (hk : 2 ≤ k) (hkn : k ≤ 2 * m - 2) (hparity : Odd m ∨ Even k) (b : ℕ) :
    (startingLabels (2 * m) k b).card = (sameColorResidues (2 * m) k).card := by
  rw [startingLabels_card_even hm]
  have hbal := sameColorResidues_parity_balance hm hk hkn hparity
  have htotal := parity_partition (sameColorResidues (2 * m) k) 0
  simp only [Nat.add_zero] at htotal
  change (sameColorResiduesParity (2 * m) k 0).card +
    (sameColorResiduesParity (2 * m) k 1).card = _ at htotal
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases hb with hb | hb <;> rw [hb] <;> omega

theorem sum_parity_weights (s : Finset ℕ) (b x y : ℕ)
    (hbal : (s.filter (fun r => (r + b) % 2 = 0)).card =
      (s.filter (fun r => (r + b) % 2 = 1)).card) :
    (∑ r ∈ s, 2 * (if (r + b) % 2 = 0 then x else y)) = s.card * (x + y) := by
  have he : s.filter (fun r => ¬(r + b) % 2 = 0) = s.filter (fun r => (r + b) % 2 = 1) := by
    ext r
    rcases Nat.mod_two_eq_zero_or_one (r + b) with h | h <;> simp [h]
  rw [← Finset.mul_sum, Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, he]
  rw [← parity_partition s b, hbal]
  ring

theorem startingLabels_sum_odd_gap {m k : ℕ} (hm : 0 < m) (hk : Odd k) (b : ℕ) :
    (∑ g ∈ Finset.Icc 1 (k - 1), (startingLabels (2 * m) k (g + b)).card) =
      (k - 1) * (sameColorResidues (2 * m) k).card := by
  simp_rw [startingLabels_card_even hm]
  have hfun (g : ℕ) : (sameColorResiduesParity (2 * m) k ((g + b) % 2)).card =
      if (g + b) % 2 = 0 then (sameColorResiduesParity (2 * m) k 0).card
      else (sameColorResiduesParity (2 * m) k 1).card := by
    rcases Nat.mod_two_eq_zero_or_one (g + b) with h | h <;> simp [h]
  simp_rw [hfun]
  rw [sum_parity_weights _ _ _ _ (firstGapParity_balance hk b)]
  have htotal := parity_partition (sameColorResidues (2 * m) k) 0
  simp only [Nat.add_zero] at htotal
  change (sameColorResiduesParity (2 * m) k 0).card +
    (sameColorResiduesParity (2 * m) k 1).card = _ at htotal
  rw [htotal, Nat.card_Icc]
  congr 1

theorem sameColorGapTuples_card_eq_sum (n k : ℕ) :
    (sameColorGapTuples n k).card =
      ∑ g₂ ∈ Finset.Icc 1 (n - k - 1), ∑ g₁ ∈ Finset.Icc 1 (k - 1),
        (startingLabels n k (g₁ + g₂)).card := by
  simp only [sameColorGapTuples, startingLabels, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product, Nat.add_assoc]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext g₁; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem sameColorGapTuples_card {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k)
    (hkn : k ≤ n - 2) :
    (sameColorGapTuples n k).card = (k - 1) * (n - k - 1) *
      (sameColorResidues n k).card := by
  rw [sameColorGapTuples_card_eq_sum]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have heq : n = 2 * m := by omega
    clear hm
    subst n
    have hmp : 0 < m := by omega
    by_cases hpar : Odd m ∨ Even k
    · simp_rw [startingLabels_card_even_balanced hmp hk hkn hpar]
      simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      have h₁ : k - 1 + 1 - 1 = k - 1 := by omega
      have h₂ : 2 * m - k - 1 + 1 - 1 = 2 * m - k - 1 := by omega
      rw [h₁, h₂]
      ring
    · have hko : Odd k := Nat.not_even_iff_odd.mp (fun h => hpar (Or.inr h))
      simp_rw [startingLabels_sum_odd_gap hmp hko]
      simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
      have h₂ : 2 * m - k - 1 + 1 - 1 = 2 * m - k - 1 := by omega
      rw [h₂]
      ring
  · simp_rw [startingLabels_card_odd ho]
    simp only [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
    have h₁ : k - 1 + 1 - 1 = k - 1 := by omega
    have h₂ : n - k - 1 + 1 - 1 = n - k - 1 := by omega
    rw [h₁, h₂]
    ring

end Paper170

end
end

section

noncomputable section
open scoped BigOperators
namespace Paper170

theorem crossingTuples_card {n : ℕ} (hn : 3 ≤ n) :
    (crossingTuples n).card = hill n := by
  have hcount : 4 * (crossingTuples n).card =
      (n / 2) * (n / 2 - 1) * (n - n / 2 - 1) * (n - n / 2 - 2) := by
    rw [crossingTuples_cyclic_count hn]
    calc
      (∑ k ∈ Finset.Icc 2 (n - 2), (sameColorGapTuples n k).card) =
          ∑ k ∈ Finset.Icc 2 (n - 2),
            (k - 1) * (n - k - 1) * (n - 2 * min k (n - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk₁ := (Finset.mem_Icc.mp hk).1
        have hk₂ := (Finset.mem_Icc.mp hk).2
        rw [sameColorGapTuples_card hn hk₁ hk₂, sameColorResidues_card hn hk₁ hk₂]
      _ = _ := by rw [cyclic_count_pairing hn, crossing_sum_telescope hn]
  have h₁ : n - n / 2 - 1 = (n - 1) / 2 := by omega
  have h₂ : n / 2 - 1 = (n - 2) / 2 := by omega
  have h₃ : n - n / 2 - 2 = (n - 3) / 2 := by omega
  rw [h₁, h₂, h₃] at hcount
  have hp : n / 2 * ((n - 1) / 2) * ((n - 2) / 2) * ((n - 3) / 2) =
      4 * (crossingTuples n).card := by rw [hcount]; ring
  rw [hill, hp]
  omega

end Paper170

end
end

end OAI
