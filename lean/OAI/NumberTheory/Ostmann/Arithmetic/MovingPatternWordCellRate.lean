import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSelectedRate
import OAI.NumberTheory.Ostmann.Construction.WordCellBulkGeometry

namespace OAI

/-! # Signed bulk cancellation for the actual selected harmonic word cells -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_word_cell_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A lo hi Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (Bidx Cidx : Type) (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
        (base : Fin (N + 1) → primes)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (U : ℝ)
        (a b : (TreeLeafIndex (n + 2) × Fin m) → ℝ)
        (h : (TreeLeafIndex (n + 2) × Fin m) → ℕ) (global : Finset ℕ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => wordCellSupport (a j) (b j) (h j)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        ((base (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ i c, ((base (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (∀ j, Real.exp ((39 / 10000 : ℝ) * L) ≤ a j) →
      (∀ j, S j ⊆ primes) →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ j, Real.exp (-Cmass * L) ≤
        finiteCellMass (primeLogCellSet 1 0 (a j) (b j) \ global)
          primeLogIndex (fun p => (p : ℝ)⁻¹) (h j)) →
      (∀ q ∈ outside, q.Prime) →
      ∀ ν : Bidx → primes → ℝ,
      (∀ j, ν (slot j) = primeSubsetPrior primes (S j \ global)) →
      ‖movingPatternBulkMean e ν slot
        (movingPatternPrimeObservable e t small slot perm pattern primes hprimes
          childBound pivotBound hfreq Fw Ew outside R r p
          (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L)
          y ψ X lo hi hlo hhi φ G L U) base‖ ≤
        Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_selected_prime_rate ψ n r₀ k A lo hi Bφ Dφ F Cmass gain
      hA hlo hhi hF hCmass hBφ hDφ
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hrate, eventually_ge_atTop (0 : ℝ)] with L hrate hL
  dsimp only
  intro Bidx Cidx N e tierB tierC t small slot perm pattern primes hprimes base
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β y X j₀ φ G U a b h global
    hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    ha hS hdel hmass hout ν hν
  let m := spectatorBulkCount k L
  let M := ∏ i, bulkResidueModuli r p i
  let u := fun j (_ : Unit) => max (a j) (h j : ℝ)
  let v := fun j (_ : Unit) => min (b j) ((h j : ℝ) + 1)
  let S := fun j => wordCellSupport (a j) (b j) (h j)
  let D := global ∪ frozenPrimeDeletions (fun i => (base i : ℕ))
    (movingPatternBulkEmbedding e slot) outside
  have hlow (j) : Real.exp ((39 / 10000 : ℝ) * L) ≤ u j () :=
    (ha j).trans (le_max_left _ _)
  have hMcell (j) (_ : Unit) : (M : ℝ) ≤ Real.exp (u j ()) :=
    modulus_le_exp_bulk_endpoint hMQ hL (hlow j)
  have hsupport (j) : primeCellSupport M (fun c : Unit × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) = S j :=
    wordCellSupport_unit_residues M (a j) (b j) (h j) (hMcell j ())
  dsimp only [M] at hsupport
  have hgeometry (j) : u j () ≤ v j () ∧ v j () ≤ u j () + 1 :=
    wordCellSupport_geometry (a j) (b j) global (h j)
      ((Real.exp_pos _).trans_le (hmass j))
  have hD (j) := wordCellSupport_frozen_deletions (a j) (b j) (h j) global
    (fun i => (base i : ℕ)) (movingPatternBulkEmbedding e slot) outside
  have hDcard : (D.card : ℝ) ≤ Real.exp (Cmass * L) := by
    have hcard : D.card ≤ global.card + (N + 1) + outside.length := by
      simpa only [Fintype.card_fin] using (hD j₀).2.2.1
    exact (Nat.cast_le.mpr hcard).trans hdel
  have hcard : (Fintype.card Unit : ℝ) ≤
      Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
    simp only [Fintype.card_unit, Nat.cast_one]
    exact Real.one_le_exp_iff.mpr (Real.exp_nonneg _)
  have hunit (j) (_ : Unit) : 1 ≤ u j () :=
    (Real.one_le_exp_iff.mpr (mul_nonneg (by norm_num) hL)).trans (hlow j)
  have hsep (j) (c d : Unit) (hcd : c ≠ d) : v j c ≤ u j d ∨ v j d ≤ u j c :=
    False.elim (hcd (Subsingleton.elim _ _))
  have hfinal := hrate Bidx Cidx Unit N e tierB tierC t small slot perm pattern
    primes hprimes base childBound pivotBound hfreq Fw Ew outside R r p hc twist sets β y X
    j₀ φ G U u v (fun _ => D) hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp
    hgood hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hunit (fun j _ => hlow j) (fun j _ => (hgeometry j).1)
    (fun j _ => (hgeometry j).2) hsep hMcell
    (fun j => by simpa only [hsupport, S] using hS j) (fun _ => hDcard)
    (fun j => by
      simpa only [hsupport, S] using
        wordCellSupport_mass_lower (a j) (b j) global (h j) _ (hmass j))
    (fun j i hi => (hD j).2.2.2.1 i hi) hout (fun j q hq => (hD j).2.2.2.2 q hq)
    ((), 1) (fun j => S j \ global)
    (fun j => by simpa only [hsupport, S] using (hD j).1)
    (fun j => by simpa only [hsupport, S, D] using (hD j).2.1) ν
    (by simpa only [hsupport, S] using hν)
  exact hfinal

end Ostmann

end OAI
