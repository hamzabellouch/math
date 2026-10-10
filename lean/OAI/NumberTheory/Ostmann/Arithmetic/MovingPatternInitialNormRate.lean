import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeNormRate
import OAI.NumberTheory.Ostmann.Construction.NestedPrimePrior
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeNorm

namespace OAI

/-! # Retaining the norm bound under the initial bulk law -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- Uniform prime-cell comparison for the actual arithmetic absolute mean.
The sharp Fourier window factor is retained in the main term. The published
progression input controls the cell, collision and deletion errors. -/
theorem PublishedProgressionInput.movingPattern_initial_prime_norm_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A lo hi Bφ Dφ F Cmass : ℝ)
    (hA : 0 ≤ A) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ n)
        (small : Bool → TreeLeafTuple (List Bidx) n)
        (slot : (TreeLeafIndex n × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
        (pattern : Bool × MovingSampleIndex n → Cidx)
        (base : Fin (N + 1) → ℕ) (primes : Finset ℕ)
        (hprimes : ∀ p ∈ primes, p.Prime)
        (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (y X A₀ : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ),
      let data := movingPatternFinBulkData e n m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
        Fw Ew data childBound R r P (bulkProgressionCutoff L) y
      let spec := fun i => frozenBulkSpectatorHaar base n m t
        (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
        (twist i) perm (normalizedResidueTransform (sets i))
      let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
        ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (Fintype.card Cell : ℝ) ≤ Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) →
      (∀ j c, 1 ≤ u j c) → (∀ j c, Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c) →
      (∀ j c, u j c ≤ v j c) → (∀ j c, v j c ≤ u j c + 1) →
      (∀ j c d, c ≠ d → v j c ≤ u j d ∨ v j d ≤ u j c) →
      (∀ j c, (M : ℝ) ≤ Real.exp (u j c)) →
      (∀ j, S j ⊆ primes) →
      (∀ j, ((deleted j).card : ℝ) ≤ Real.exp (Cmass * L)) →
      (∀ j, Real.exp (-Cmass * L) ≤ ∑ q ∈ S j, (q : ℝ)⁻¹) →
      (∀ j i, i ∉ Set.range (movingPatternBulkEmbedding e slot) → base i ∈ deleted j) →
      (∀ q ∈ outside, q.Prime) → (∀ j q, q ∈ outside → q ∈ deleted j) →
      0 ≤ A₀ →
      (∀ z : (TreeLeafIndex n × Fin m) → ℝ, (∀ j, 0 ≤ z j) →
        (Fintype.card ((TreeLeafIndex n × Fin m) → (ZMod M)ˣ) : ℝ)⁻¹ *
          ∑ w, ‖a w * ∏ j, pageGiantWeight P (bulkProgressionCutoff L) M
            (w j).val.val (z j)‖ ≤ A₀) →
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ∀ initial : (TreeLeafIndex n × Fin m) → Finset ℕ,
      (∀ j, initial j ⊆ S j) → (∀ j, S j \ deleted j ⊆ initial j) →
      ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
        ((∏ j, primeSubsetPrior primes (initial j) (x j) : ℝ) : ℂ) *
          movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
            childBound pivotBound hfreq Fw Ew outside R r p
            (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L)
            y ψ X lo hi hlo hhi φ G L U x‖ ≤
        ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  have hconditional := P.movingPattern_original_prime_norm_rate ψ n r₀ k
    A lo hi Bφ Dφ F Cmass hA hlo hhi hF hCmass hBφ hDφ
  filter_upwards [hconditional, movingPattern_bad_event_rate ψ n r₀ k
    A lo hi Bφ Dφ F (Cmass + 1) hA hhi hF,
    P.original_harmonic_box_rate Cmass hCmass, eventually_ge_atTop (2000 : ℝ)]
    with L hconditional hbad hnormal hL
  dsimp only
  intro Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern base primes hprimes hbase
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets y X A₀ j₀ φ G U u v deleted
    hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hy hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout hA₀ hlocal c₀
    initial hsub hretain
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let M := ∏ i, bulkResidueModuli r p i
  let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
  let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hQ := bulkProgressionCutoff_bounds L hL
  have hnorm (j) : 0 < (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹) ∧
      Z j ≤ Real.exp ((Cmass + 1) * L) ∧
      Z j * (∑ c, ∫ x in Set.Ioc (u j c) (v j c), (x : ℝ)⁻¹) ≤ 2 := by
    have heq := unitPrimeCellSupport_eq M (u j) (v j) (hMcell j)
    have hh := hnormal Cell (bulkProgressionCutoff L) hQ.1 hQ.2 hcard
      (u j) (v j) (deleted j) (hu j) (hulow j) (huv j) (hshort j) (hsep j) (hdel j)
    simpa only [← heq, S, Z] using hh (by simpa only [← heq, S] using hmass j)
  have hlow (j) (q : ℕ) (hq : q ∈ S j) :
      Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ) := by
    obtain ⟨c, _, hqc⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqp, _, hql, _⟩ := mem_primeLogCellSet_iff.mp hqc
    exact (Real.le_log_iff_exp_le (by exact_mod_cast hqp.pos)).mp ((hulow j c.1).trans hql.le)
  have hZ0 (j) : 0 ≤ Z j := inv_nonneg.mpr (hnorm j).1.le
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hbd := hbad p S deleted Z amp ((Cmass + 1) * L)
    (Real.exp ((39 / 10000 : ℝ) * L)) hpupper hZ0 (fun j => (hnorm j).2.1)
    (fun j => (hdel j).trans (Real.exp_le_exp.mpr (by nlinarith))) le_rfl hamp0 hamp le_rfl hlow
  have hdeletedBound := hconditional Bidx Cidx Cell N e tierB tierC t small slot perm pattern
    base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r p hc twist sets y X A₀
    j₀ φ G U u v deleted hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hy hpupper hMQ
    hφ hlip hφout hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout
    hA₀ hlocal c₀
  let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1))) * W
  have hpoint (x : (TreeLeafIndex n × Fin m) → primes) :
      ‖movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L)
        y ψ X lo hi hlo hhi φ G L U x‖ ≤ cost :=
    movingPatternPrimeBulkHaar_norm e tierB tierC t small slot perm pattern hB htier
      base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L) y
      j₀ ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout L U
      hy (fun i => (p i : ℝ)) (fun i => Nat.cast_nonneg _)
      (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z) x
  have hcollision : 0 ≤ cost * (Fintype.card (TreeLeafIndex n × Fin m) : ℝ) ^ 2 *
      Real.exp ((Cmass + 1) * L - Real.exp ((39 / 10000 : ℝ) * L)) := by
    dsimp only [cost, W, amp]
    positivity
  have hreturnCost := (le_add_of_nonneg_left hcollision).trans hbd
  have hcost0 : 0 ≤ cost := by dsimp only [cost, W, amp]; positivity
  have hfinal := @nested_prime_prior_three_errors (TreeLeafIndex n × Fin m)
    inferInstance primes S initial deleted hS hsub hretain (fun j => (hnorm j).1)
    (fun x => movingPatternPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
      childBound pivotBound hfreq Fw Ew outside R r p
      (fun i => normalizedResidueTransform (sets i)) twist P (bulkProgressionCutoff L)
      y ψ X lo hi hlo hhi φ G L U x)
    cost (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
      Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m)) (Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)))
    (Real.exp (-Real.exp ((2 / 1000 : ℝ) * L))) hcost0 hpoint
    (by simpa only [finite_univ_canonical, m, S, M] using hdeletedBound)
    (by simpa only [finite_univ_canonical, cost, W, m, Z] using hreturnCost)
  simpa only [finite_univ_canonical, m, S, M] using hfinal

end Ostmann

end OAI
