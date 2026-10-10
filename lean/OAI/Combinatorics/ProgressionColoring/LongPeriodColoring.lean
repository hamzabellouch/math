import OAI.Combinatorics.ProgressionColoring.LongPeriodEligibility
import OAI.Combinatorics.ProgressionColoring.BlockCoverage
import OAI.Combinatorics.ProgressionColoring.LiteralLabelRectangles
import OAI.Combinatorics.ProgressionColoring.CyclicBlockLabels

namespace OAI

/-! The long-period case for the coloring pulled back from the actual
two-system full labels of the cyclic progression. -/

namespace QuantitativeVanDerWaerden

open AnchoredPatterns
open scoped Classical

/-- Heavy positions are defined by their literal full-label multiplicity in
the entire progression, rather than within an individual block. -/
noncomputable def literalProgressionHeavy
    (mesh : AdaptiveMesh) (q D lambda n k : ℕ) (hn : 0 < n)
    (a d : CyclicGroup q D) (M : ℝ) (j : Fin k) : Prop := by
  classical
  exact (k : ℝ) / M <
    ((Finset.univ.filter fun l : Fin k =>
      literalFullLabel mesh q D lambda n hn (a + l.val • d) =
        literalFullLabel mesh q D lambda n hn (a + j.val • d)).card : ℝ)

/-- Quarter-balance on at least half the positions gives an eighth of the
whole block. The restriction to regular positions is removed by inclusion. -/
theorem block_color_count_of_regular_balance {h : ℕ}
    (S : Finset (Fin h)) (color : Fin h → Bool) (c : Bool)
    (hmany : h ≤ 2 * S.card)
    (hbalanced : S.card ≤ 4 * (S.filter fun z => color z = c).card) :
    (h : ℝ) / 8 ≤ ((Finset.univ.filter fun z => color z = c).card : ℝ) := by
  have hsub : S.filter (fun z => color z = c) ⊆
      Finset.univ.filter (fun z => color z = c) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2⟩
  have hcard := Finset.card_le_card hsub
  have hn : h ≤ 8 * (Finset.univ.filter fun z => color z = c).card := by omega
  have hr : (h : ℝ) ≤ 8 * ((Finset.univ.filter fun z => color z = c).card : ℝ) := by
    exact_mod_cast hn
  linarith

/-- The long-period case of the dichotomy for the actual cyclic pullback
coloring. Half-block regularity and eligibility are proved by the preceding
grid and mesh lemmas. Full blocks are counted through literal indices. -/
theorem literal_long_period_balanced
    (mesh : AdaptiveMesh) (q D lambda n k h : ℕ) (hn : 0 < n)
    (a d : CyclicGroup q D) (M : ℝ) (u v : Fin D → ℝ)
    (t : Fin D → Fin h) (hh : 0 < h) (hD : 3 ≤ D)
    (cstar : FullLabel D (Fin n) mesh.Label → Bool)
    (hprimitive : PrimitiveVector h (fun i => ((t i).val : ℤ)))
    (hX : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      xRep q D (a + j • d) i - xRep q D a i -
        (j : ℝ) / h * ((t i).val + u i) = e)
    (hY : ∀ j, j < k → ∀ i : Fin D, ∃ e : ℤ,
      yRep q D lambda (a + j • d) i - yRep q D lambda a i -
        (j : ℝ) / h * ((lambda : ℝ) * (t i).val + v i) = e)
    (hfirst : ∀ i, |u i| ≤ 1 / (n : ℝ))
    (hscale : 2 * (h : ℝ) * (1 / (n : ℝ)) < 1)
    (hrotating : ∀ i, ¬ stationary lambda t i → |v i| ≤ mesh.H)
    (hnear : ∀ i, ¬ stationary lambda t i → |v i| < 1 / (1000 * (D : ℝ)))
    (hperiod : ∀ i, ¬ stationary lambda t i →
      D ^ 2 < h / Nat.gcd h (lambda * (t i).val))
    (hcoef : 2 * M / (k : ℝ) ≤ 1 / 16)
    (hheavy : ∀ j : Fin k, literalProgressionHeavy mesh q D lambda n k hn a d M j →
      ∀ i, |v i| ≤ (2 * M / (k : ℝ)) *
        mesh.width (mesh.meshLabel (yRep q D lambda (a + j.val • d) i)))
    (hlight : (BlockCoverage.lightCount
      (literalProgressionHeavy mesh q D lambda n k hn a d M) : ℝ) ≤ (k : ℝ) / 10)
    (hblocksmall : (h : ℝ) ≤ (k : ℝ) / 10)
    (hbalance : ∀ R : Realization D,
      EligibleRealization n hn mesh (1 / (1000 * (D : ℝ))) lambda t R → ∀ c : Bool,
      (regularPositions (1 / (1000 * (D : ℝ))) R lambda t).card ≤
        4 * ((regularPositions (1 / (1000 * (D : ℝ))) R lambda t).filter
          fun z => cstar (fullLabel n hn mesh R lambda t z) = c).card) :
    ∀ c : Bool, (k : ℝ) / 100 ≤
      ((Finset.univ.filter fun j : Fin k =>
        cstar (literalFullLabel mesh q D lambda n hn (a + j.val • d)) = c).card : ℝ) := by
  classical
  let heavy := literalProgressionHeavy mesh q D lambda n k hn a d M
  let color : Fin k → Bool := fun j =>
    cstar (literalFullLabel mesh q D lambda n hn (a + j.val • d))
  have hblocks : ∀ b ∈ BlockCoverage.usedBlocks k h heavy, ∀ c : Bool,
      (h : ℝ) / 8 ≤ (BlockCoverage.blockColorCount k h color c b : ℝ) := by
    intro b hb c
    obtain ⟨anchor, hanchor⟩ := (BlockCoverage.mem_usedBlocks k h heavy b).mp hb
    let R := CyclicBlockLabels.cyclicBlockRealization q D lambda k h a d u v b
    have hlabels : ∀ z : Fin h,
        literalFullLabel mesh q D lambda n hn
          (a + (BlockCoverage.blockIndex k h b z).val • d) =
        fullLabel n hn mesh R lambda t z :=
      fun z => CyclicBlockLabels.literalFullLabel_block_eq mesh q D lambda n k h hn hh
        a d u v t hX hY b z
    have hanchorWidth : ∀ i, stationary lambda t i → |R.v i| ≤
        (2 * M / (k : ℝ)) *
          mesh.width (mesh.meshLabel (secondPath R lambda t anchor i)) := by
      intro i _
      have hi : mesh.meshLabel
          (yRep q D lambda (a + (BlockCoverage.blockIndex k h b anchor).val • d) i) =
          mesh.meshLabel (secondPath R lambda t anchor i) :=
        congrArg (fun L => L.2 i) (hlabels anchor)
      rw [← hi]
      exact hheavy (BlockCoverage.blockIndex k h b anchor) hanchor i
    have heligible : EligibleRealization n hn mesh (1 / (1000 * (D : ℝ))) lambda t R :=
      heavy_long_block_eligible n hn mesh R lambda t hh hD hprimitive hfirst hscale
        hrotating hnear hperiod anchor M (k : ℝ) hcoef hanchorWidth
    have hlocal := block_color_count_of_regular_balance
      (regularPositions (1 / (1000 * (D : ℝ))) R lambda t)
      (fun z => cstar (fullLabel n hn mesh R lambda t z)) c
      heligible.regular_many (hbalance R heligible c)
    have hsets :
        (Finset.univ.filter fun z : Fin h => color (BlockCoverage.blockIndex k h b z) = c) =
        Finset.univ.filter (fun z : Fin h => cstar (fullLabel n hn mesh R lambda t z) = c) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (cstar (literalFullLabel mesh q D lambda n hn
        (a + (BlockCoverage.blockIndex k h b z).val • d)) = c) ↔ _
      rw [hlabels z]
    rw [CyclicBlockLabels.blockColorCount_eq_local, hsets]
    exact hlocal
  have hglobal := BlockCoverage.colorCount_tenth k h hh heavy color hlight hblocksmall hblocks
  intro c
  have hc := hglobal c
  change (k : ℝ) / 100 ≤ (BlockCoverage.colorCount color c : ℝ)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

end QuantitativeVanDerWaerden

end OAI
