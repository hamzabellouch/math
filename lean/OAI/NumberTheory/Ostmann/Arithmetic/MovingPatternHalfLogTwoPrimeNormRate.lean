import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogTwoPrimeNormBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternHalfLogCellError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBadEventRate
import OAI.NumberTheory.Ostmann.Construction.OriginalHarmonicRate
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProgressionCutoff

namespace OAI

/-! # The original-prior norm estimate at the manuscript scales -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- Uniform prime-cell comparison for the actual arithmetic absolute mean.
The sharp Fourier window factor is retained in the main term. The published
progression input controls the cell, collision and deletion errors. -/
theorem PublishedProgressionInput.movingPattern_half_log_original_two_prime_norm_rate
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A Wwin Bφ Dφ F Cmass : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ n) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi),
      hi - lo ≤ Real.exp (Wwin * m) →
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
        (Qfreq : ℕ) (xg y X A₀ : ℝ) (_j₀ : TreeLeafIndex n × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex n × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex n × Fin m) → Finset ℕ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ),
      let data := movingPatternFinBulkData e n m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 4 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let freq := frozenBulkFrequencyPrime base (movingPatternBulkEmbedding e slot) outside
        Fw Ew data childBound R r P Qfreq xg y
      let spec := fun i => frozenBulkSpectatorPrime base n m t
        (fun b => movingPatternFiniteSmall e n (small b)) (movingPatternFiniteSamples e n pattern)
        (twist i) perm (normalizedResidueTransform (sets i))
      let a := fun z => freq (bulkResidueEquiv r p _hc z).1 *
        ∏ i, spec i ((bulkResidueEquiv r p _hc z).2 i)
      (∀ j, (logSlots j).length ≤ 2 ^ n * (r₀ + m + 4 * n)) →
      (∀ b, ∀ i ∈ flattenMovingSlots n (small b), i ∉ Set.range slot) →
      (∀ i, n ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE n (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      amp ≤ Real.exp (F * m) → 0 ≤ xg → 0 ≤ y →
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
      ‖∑ x : (TreeLeafIndex n × Fin m) → primes,
        ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
          movingPatternLogTwoPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
            childBound pivotBound hfreq Fw Ew outside R r p
            (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
            xg y ψ X lo hi hlo hhi φ G XL U logSlots cb x‖ ≤
        ((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
          Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m) +
          Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨Cerr, hCerr, hCnorm, hcellRate⟩ :=
    P.movingPattern_half_log_cell_error_rate_window ψ n r₀ k A Wwin Bφ Dφ F (Cmass + 1) Dlog
      hA hWwin hF hDlog tlog htlog
  obtain ⟨Tcell, _, hcellTwo⟩ := P.short_prime_cell_mass_two
  have hlarge : ∀ᶠ L : ℝ in atTop, Tcell ≤ Real.exp ((39 / 10000 : ℝ) * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop Tcell)
  filter_upwards [hcellRate, movingPattern_bad_event_rate_window ψ n r₀ k
    A Wwin Bφ Dφ F (Cmass + 1) hA hWwin hF,
    P.original_harmonic_box_rate Cmass hCmass, hlarge, eventually_ge_atTop (2000 : ℝ)]
    with L herror hbad hnormal hlarge hL
  dsimp only
  intro lo hi hlo hhi hwindow Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern base primes hprimes hbase
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets Qfreq xg y X A₀ j₀ φ G XL U u v deleted logSlots cb
    hslots hsmall hB htier hsmallLen hR hr hV hsets hsetsp hamp hxg hy hpupper hMQ hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout hA₀ hlocal c₀
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e n m t small slot perm pattern
  let M := ∏ i, bulkResidueModuli r p i
  let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let amp := 4 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
  let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi n *
    (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  let freq := frozenBulkFrequencyPrime base (movingPatternBulkEmbedding e slot) outside
    Fw Ew data childBound R r P Qfreq xg y
  let spec := fun i => frozenBulkSpectatorPrime base n m t
    (fun b => movingPatternFiniteSmall e n (small b))
    (movingPatternFiniteSamples e n pattern) (twist i) perm
    (normalizedResidueTransform (sets i))
  let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
    ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
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
  have hZ (j) : Z j ≤ Real.exp (Cerr * L) := (hnorm j).2.1.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCnorm (by linarith)))
  have hunit : (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) :=
    bulkResidueModulus_unit_card hMQ (Nat.floor_le (Real.exp_nonneg _))
  have ha (z) : ‖a z‖ ≤ amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 1)) := by
    exact moving_frozen_prime_residue_coefficient_norm base (movingPatternBulkEmbedding e slot) outside
      Fw Ew n m data childBound R r P Qfreq xg y hxg hy p sets hsets hsetsp
      t _ _ twist perm (bulkResidueEquiv r p hc z).1 (bulkResidueEquiv r p hc z).2
  have he := herror lo hi hhi hwindow Cell M (bulkProgressionCutoff L) hQ.1 hQ.2 p Z a amp
    (Real.exp ((39 / 10000 : ℝ) * L)) (2 ^ n * (r₀ + m + 4 * n)) le_rfl
      hpupper hZ0 hZ hcard hunit hamp0 hamp ha le_rfl u hulow
  have hbd := hbad lo hi hhi hwindow p S deleted Z amp ((Cmass + 1) * L)
    (Real.exp ((39 / 10000 : ℝ) * L)) hpupper hZ0 (fun j => (hnorm j).2.1)
    (fun j => (hdel j).trans (Real.exp_le_exp.mpr (by nlinarith))) le_rfl hamp0 hamp le_rfl hlow
  have hb := P.movingPattern_log_two_prime_norm_bound e tierB tierC t small slot perm pattern
    hsmall hB htier base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r
    hR hr p hc (fun i => normalizedResidueTransform (sets i))
    (fun i => normalizedResidueTransform_zero (sets i)) twist (bulkProgressionCutoff L) Qfreq xg y
    j₀ ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout XL U logSlots cb Dlog hDlog hloglip (2 ^ n * (r₀ + m + 4 * n)) hslots
    r₀ hsmallLen hxg hy hQ.1 hMQ u v hu huv hshort
    (fun j c z => hcellTwo M z.val.val (u j c) (v j c) (hlarge.trans (hulow j c)) (hshort j c))
    c₀ hS (fun j => unitPrimeCells_separated M (u j) (v j) (hsep j)) deleted
    (fun j => (hnorm j).1.ne') hdelbase hout hdelout (fun i => (p i : ℝ))
    (fun i => Nat.cast_nonneg _) (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z)
    A₀ hA₀ ((Cmass + 1) * L) (Real.exp ((39 / 10000 : ℝ) * L))
    hlocal (fun j => (hnorm j).2.2) (fun j => (hnorm j).2.1)
    (fun j q hq => hlow j q (Finset.mem_sdiff.mp hq).1)
  dsimp only at hb
  have hh := add_le_add (le_refl
    (((((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) *
      Bφ ^ (2 ^ n - 1)) ^ 2) * A₀) * 2 ^ Fintype.card (TreeLeafIndex n × Fin m))) (add_le_add he hbd)
  apply hb.trans
  simpa only [add_assoc, W, amp, Z, a, spec, freq, data, M, S] using hh

end Ostmann

end OAI
