import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternLogMixedPrimeSignedBound
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternWindowPrimeGain
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternHalfLogCellError
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBadEventRate
import OAI.NumberTheory.Ostmann.Construction.OriginalHarmonicRate
import OAI.NumberTheory.Ostmann.ZeroDensity.BulkProgressionCutoff

namespace OAI

/-! # One original-prior signed bulk estimate at the manuscript scales -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

/-- The three arithmetic costs are combined for the literal original prime
mean. The only analytic input is the published progression theorem; local
cancellation is proved from the balanced spectator sets and their mixed
Fourier bounds. All prime normalizers are those before idealization. -/
theorem PublishedProgressionInput.movingPattern_half_log_original_prime_rate_window
    (P : PublishedProgressionInput) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|)
    (tlog : ℕ) (htlog : tlog ≤ 4 * 2 ^ (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx Cell : Type) [Fintype Cell] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (base : Fin (N + 1) → ℕ) (primes : Finset ℕ)
        (hprimes : ∀ p ∈ primes, p.Prime)
        (hbase : ∀ i ∉ Set.range (movingPatternBulkEmbedding e slot), (base i).Prime)
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (u v : (TreeLeafIndex (n + 2) × Fin m) → Cell → ℝ)
        (deleted : (TreeLeafIndex (n + 2) × Fin m) → Finset ℕ)
        (logSlots : Fin tlog → List (Fin (N + 1))) (cb : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1)
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      (∀ j, (logSlots j).length ≤ 2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) →
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
      (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
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
      ∀ _c₀ : Cell × (ZMod M)ˣ,
      ‖∑ x : (TreeLeafIndex (n + 2) × Fin m) → primes,
        ((∏ j, primeSubsetPrior primes (S j \ deleted j) (x j) : ℝ) : ℂ) *
          movingPatternLogPrimeBulkHaar e t small slot perm pattern base primes hprimes hbase
            childBound pivotBound hfreq Fw Ew outside R r p
            (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
            y ψ X lo hi hlo hhi φ G XL U logSlots cb x‖ ≤
        Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
  obtain ⟨ε, δ, hε, hε1, hδ, cutoff, hcutoff, hgain⟩ :=
    exists_movingPatternPrimeGain_window ψ n r₀ A H Bφ Dφ F gain hA hH
  obtain ⟨Cerr, hCerr, hCnorm, hcellRate⟩ :=
    P.movingPattern_half_log_cell_error_rate_window ψ (n + 2) r₀ k A H Bφ Dφ F (Cmass + 1) Dlog hA hH hF hDlog tlog htlog
  obtain ⟨Tcell, _, hcellTwo⟩ := P.short_prime_cell_mass_two
  have hlarge : ∀ᶠ L : ℝ in atTop, Tcell ≤ Real.exp ((39 / 10000 : ℝ) * L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop Tcell)
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  filter_upwards [hcellRate, movingPattern_bad_event_rate_window ψ (n + 2) r₀ k
    A H Bφ Dφ F (Cmass + 1) hA hH hF,
    P.original_harmonic_box_rate Cmass hCmass, hlarge, eventually_ge_atTop (2000 : ℝ)]
    with L herror hbad hnormal hlarge hL
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx Cell _ N e tierB tierC t small slot perm pattern base primes hprimes hbase
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq y X j₀ φ G XL U u v deleted logSlots cb
    hslots hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hcard hu hulow huv hshort hsep hMcell hS hdel hmass hdelbase hout hdelout c₀
  let m := spectatorBulkCount k L
  let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
  let M := ∏ i, bulkResidueModuli r p i
  let S := fun j => primeCellSupport M (fun c : Cell × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
    ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
  let Z := fun j => (∑ q ∈ S j \ deleted j, (q : ℝ)⁻¹)⁻¹
  let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
    (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
  let freq := frozenBulkFrequencyFactor base (movingPatternBulkEmbedding e slot) outside
    Fw Ew data childBound R r P Qfreq y
  let spec := fun i => frozenBulkSpectatorHaar base (n + 2) m t
    (fun b => movingPatternFiniteSmall e (n + 2) (small b))
    (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
    (normalizedResidueTransform (sets i))
  let a := fun z => freq (bulkResidueEquiv r p hc z).1 *
    ∏ i, spec i ((bulkResidueEquiv r p hc z).2 i)
  have hamp0 : 0 ≤ amp := by dsimp only [amp]; positivity
  have hg := hgain m hm lo hi hhi hwidth Bidx Cidx N e base t small pattern p hp
    (fun i b s hs => ⟨hfreq b s hs, hfreqp i b s hs⟩) hsmallp hsamplesp
    twist perm hgood sets hdlo hdhi hsets hsetsp β hβ hbias amp hamp0 hamp
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
  have ha (z) : ‖a z‖ ≤ amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1)) := by
    exact moving_frozen_residue_coefficient_norm base (movingPatternBulkEmbedding e slot) outside
      Fw Ew (n + 2) m data childBound R r P Qfreq y hy p sets hsets hsetsp
      t _ _ twist perm (bulkResidueEquiv r p hc z).1 (bulkResidueEquiv r p hc z).2
  have he := herror lo hi hhi hwidth Cell M (bulkProgressionCutoff L) hQ.1 hQ.2 p Z a amp
    (Real.exp ((39 / 10000 : ℝ) * L)) (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) le_rfl hpupper hZ0 hZ hcard hunit hamp0 hamp ha le_rfl u hulow
  have hbd := hbad lo hi hhi hwidth p S deleted Z amp ((Cmass + 1) * L)
    (Real.exp ((39 / 10000 : ℝ) * L)) hpupper hZ0 (fun j => (hnorm j).2.1)
    (fun j => (hdel j).trans (Real.exp_le_exp.mpr (by nlinarith))) le_rfl hamp0 hamp le_rfl hlow
  have hb := P.movingPattern_log_mixed_prime_signed_bound e tierB tierC t small slot perm pattern
    hsmall hB htier base primes hprimes hbase childBound pivotBound hfreq Fw Ew outside R r
    hR hr p hc (fun i => normalizedResidueTransform (sets i))
    (fun i => normalizedResidueTransform_zero (sets i)) twist (bulkProgressionCutoff L) Qfreq y
    j₀ ψ X lo hi (Real.exp (A * m)) hlo hhi hV φ G Bφ Dφ hBφ hDφ hφ hlip hφout XL U logSlots cb Dlog hDlog hloglip
    (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2))) hslots r₀ hsmallLen hy hQ.1 hMQ hpage u v hu huv hshort
    (fun j c z => hcellTwo M z.val.val (u j c) (v j c) (hlarge.trans (hulow j c)) (hshort j c))
    c₀ hS (fun j => unitPrimeCells_separated M (u j) (v j) (hsep j)) deleted
    (fun j => (hnorm j).1.ne') hdelbase hout hdelout (fun i => (p i : ℝ))
    (fun i => Nat.cast_nonneg _) (fun i z => normalizedResidueTransform_norm_le_prime (sets i) (hsets i) (hsetsp i) z)
    δ hδ.le ((Cmass + 1) * L) (Real.exp ((39 / 10000 : ℝ) * L))
    hg.1 (fun j => (hnorm j).2.2) (fun j => (hnorm j).2.1)
    (fun j q hq => hlow j q (Finset.mem_sdiff.mp hq).1)
  dsimp only at hb
  calc
    _ ≤ _ := hb
    _ ≤ Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
        Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)) := by
      have hh := add_le_add (add_le_add hg.2 he) hbd
      simpa only [add_assoc, W, amp, Z, a, spec, freq, data, M, S] using hh

end Ostmann

end OAI
