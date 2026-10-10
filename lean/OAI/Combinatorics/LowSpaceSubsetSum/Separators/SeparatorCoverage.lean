import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorCheck

namespace OAI

/-! # Coverage probability of the actual four-block checker -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorCheck

open SeparatorExpectation

variable {g : ℕ}

/-- The one-draw success probability for the prescribed left count. -/
def theta (e c : ℕ) : ℝ :=
  (Nat.choose (g / 2) (e - c) : ℝ) / Nat.choose g e

abbrev Draws (g : ℕ) (e c : Fin 4 → ℕ) :=
  ∀ i : Fin 4, Fin (⌈10 / (theta (g := g) (e i) (c i))⌉₊) →
    SeparatorSample (Finset.univ : Finset (Fin g)) (e i)

/-- Sample occurrences keep their indices, including repeated subsets. -/
def sampledFamilies {e c : Fin 4 → ℕ} (draws : Draws g e c) :
    Fin 4 → Array (Finset (Fin g)) :=
  fun i => Array.ofFn (fun j => (draws i j).val)

theorem sampled_covered_iff {e c : Fin 4 → ℕ} (draws : Draws g e c)
    (x y : Record g) :
    Covered (sampledFamilies draws) x y ↔
      ∀ i, ∃ j, localMask i x.mask ⊆ (draws i j).val ∧
        Disjoint (draws i j).val (localMask i y.mask) := by
  constructor
  · intro h i
    obtain ⟨j, hl, hr⟩ := h i
    let k : Fin (⌈10 / (theta (g := g) (e i) (c i))⌉₊) :=
      ⟨j.val, by simpa [sampledFamilies] using j.isLt⟩
    exact ⟨k, by simpa [sampledFamilies, k] using hl,
      (by simpa [sampledFamilies, k, disjoint_comm] using hr)⟩
  · intro h i
    obtain ⟨j, hl, hr⟩ := h i
    let k : Fin (sampledFamilies draws i).size :=
      ⟨j.val, by simp only [sampledFamilies, Array.size_ofFn]; exact j.isLt⟩
    exact ⟨k, by simpa [sampledFamilies, k] using hl,
      (by simpa [sampledFamilies, k, disjoint_comm] using hr)⟩

/-- All four families cover any fixed admissible pair with the paper's
`1-4 exp(-10)` probability under the actual independent sampling law. -/
theorem coverage_probability (e c : Fin 4 → ℕ) (x y : Record g)
    (heven : 2 ∣ g) (hd : Disjoint x.mask y.mask)
    (hc : ∀ i, (localMask i x.mask).card = c i)
    (hhalf : ∀ i, c i + (localMask i y.mask).card = g / 2)
    (hce : ∀ i, c i ≤ e i) (heg : ∀ i, e i ≤ g)
    (hfeas : ∀ i, e i - c i ≤ g / 2) :
    1 - 4 * Real.exp (-10) ≤ finiteUniformProbability
      (fun draws : Draws g e c => Covered (sampledFamilies draws) x y) := by
  classical
  let Ψ := fun i : Fin 4 => Fin (⌈10 / (theta (g := g) (e i) (c i))⌉₊) →
    SeparatorSample (Finset.univ : Finset (Fin g)) (e i)
  have hsample (i : Fin 4) :
      Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa using heg i)).to_subtype
  let (i : Fin 4) : Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (e i)) :=
    hsample i
  let Q (i : Fin 4) (family : Ψ i) : Prop :=
    ∃ j, localMask i x.mask ⊆ (family j).val ∧
      Disjoint (family j).val (localMask i y.mask)
  have hmarginal (i : Fin 4) :
      1 - Real.exp (-10) ≤ finiteUniformProbability (Q i) := by
    have hdi : Disjoint (localMask i x.mask) (localMask i y.mask) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact Finset.disjoint_left.mp hd ((localMask_mem i x.mask j).mp hj)
        ((localMask_mem i y.mask j).mp hk)
    have hcov := separator_family_coverage (Finset.univ : Finset (Fin g))
        (localMask i x.mask) (localMask i y.mask) (e i)
        (Finset.subset_univ _) (Finset.subset_univ _) hdi
        (by simpa only [hc i] using hce i) (by simpa using heg i)
        (by simpa using heven) (by simpa only [Finset.card_univ, Fintype.card_fin, hc i] using (hhalf i))
        (by simpa only [Finset.card_univ, Fintype.card_fin, hc i] using hfeas i)
    dsimp only at hcov
    rw [Finset.card_univ, Fintype.card_fin, hc i] at hcov
    exact hcov
  have hfour := four_family_union_bound (fun i (draws : ∀ i, Ψ i) => Q i (draws i))
    (fun i => by rw [probability_pi_coordinate i (Q i)]; exact hmarginal i)
  simpa only [sampled_covered_iff, Q] using hfour

/-- Applying the executable checker preserves this fixed-pair success bound. -/
theorem acceptance_probability (n : ℕ) (e c : Fin 4 → ℕ) (target : ℤ)
    (xs ys : List (Record g)) (hsize : xs.length + ys.length ≤ 2 ^ n)
    (x y : Record g) (hx : x ∈ xs) (hy : y ∈ ys)
    (hw : x.value + y.value = target)
    (heven : 2 ∣ g) (hd : Disjoint x.mask y.mask)
    (hc : ∀ i, (localMask i x.mask).card = c i)
    (hhalf : ∀ i, c i + (localMask i y.mask).card = g / 2)
    (hce : ∀ i, c i ≤ e i) (heg : ∀ i, e i ≤ g)
    (hfeas : ∀ i, e i - c i ≤ g / 2) :
    1 - 4 * Real.exp (-10) ≤ finiteUniformProbability
      (fun draws : Draws g e c => (run n (sampledFamilies draws) target xs ys).accepted = true) :=
  (coverage_probability e c x y heven hd hc hhalf hce heg hfeas).trans
    (finiteUniformProbability_mono (fun _ h => finds_fixed_pair n _ target xs ys hsize x y hx hy hw h))

end LowSpaceSubsetSum.SeparatorCheck

end

end OAI
