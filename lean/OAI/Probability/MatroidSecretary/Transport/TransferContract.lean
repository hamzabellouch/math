import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Transport.TransferSpecification

namespace OAI

/-!
# Source-facing sample-to-rank transfer

Source: `sections/transfer.tex`, `lem:transfer` / `eq:rank-transfer`.
The comparison set is the actual priority-greedy survivor group; its independence
and containment are proved, not supplied as extra assumptions.  `mainMean` fixes
only H and averages the density, guard, test, and parity coins.  `trueZ` uses zero
on unlisted outcomes, so the expectation is not conditioned on listing.
-/

namespace MatroidProphet.SourceProof

open Finset MainAlgorithm

/-- Conditional averaging depends on the fixed filter mask only.  All other
fields of the initial record are overwritten by independent product samples. -/
lemma mainMean_filter_congr {n : ℕ} (d d' : MainMasks n)
    (hH : d.H = d'.H) (f : MainMasks n → ℝ) : mainMean d f = mainMean d' f := by
  rcases d with ⟨H, D, C, T, p⟩
  rcases d' with ⟨H', D', C', T', p'⟩
  change H = H' at hH
  subst H'
  rfl

/-- The unlisted branch is included in the product average with zero statistic. -/
lemma trueZ_unlisted {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (hi : i ∉ groups M d s) : trueZ M hE d s i = 0 := by
  classical
  simp only [trueZ, ite_eq_right hi]

/-- In particular, a true group missed by the discovery sample contributes zero;
no positivity or listing assumption is imposed on the individual outcomes. -/
lemma trueZ_zero_of_no_discovery {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (d : MainMasks n) (s : Fin n → Option ℤ) (i : ℤ)
    (hmiss : d.D ∩ trueGroup M d s i = ∅) : trueZ M hE d s i = 0 := by
  apply trueZ_unlisted
  intro hi
  obtain ⟨e, heD, heU⟩ := (mem_listed_iff M d s i).mp ((mem_groups M d s i).mp hi)
  have he : e ∈ d.D ∩ trueGroup M d s i := mem_inter.mpr ⟨heD, heU⟩
  rw [hmiss] at he
  exact notMem_empty e he

/-- The source transfer at arbitrary rounded-level keys.  This stronger helper
also covers the `none` keys representing zero/nonpositive weights. -/
theorem transfer_keys {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (s : Fin n → Option ℤ) (H : Finset (Fin n)) (i : ℤ) :
    let d : MainMasks n := ⟨H, ∅, ∅, ∅, false⟩
    let U := trueGroup M d s i
    let Y := (positiveGreedy M s \ H).filter (fun e => s e = some i)
    densityThreshold ≤ (U.card : ℝ) →
      ((((2 : ℝ)^16)⁻¹ * Y.card - ((2 : ℝ)^23)⁻¹ * U.card) / (2 : ℝ)^100) ≤
        mainMean d (fun d' => (trueZ M hE d' s i : ℝ)) := by
  classical
  dsimp only
  intro hn
  let d : MainMasks n := ⟨H, ∅, ∅, ∅, false⟩
  let Y := (positiveGreedy M s \ H).filter (fun e => s e = some i)
  have hY : (Y : Set (Fin n)) ⊆ (trueGroup M d s i : Set (Fin n)) := by
    intro e he
    rw [trueGroup_eq_candidate_filter]
    rcases mem_filter.mp he with ⟨heG, hei⟩
    exact mem_filter.mpr ⟨positiveGreedy_survivors_subset M s H heG, hei⟩
  have hI : M.Indep (Y : Set (Fin n)) :=
    (positiveGreedy_survivors_indep M hE s H).subset
      (fun _ he => (mem_filter.mp he).1)
  have h := mainMean_trueZ_lower M hE d s i (Y : Set (Fin n)) hY hI hn
  simpa only [Set.ncard_coe_finset, retainedFraction, densityThreshold, d, Y] using h

/-- `lem:transfer` for the manuscript's actual rounded nonnegative weights,
with literal constants gamma = 2^-16 and kappa = 2^100. -/
theorem transfer {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (_hw : ∀ e, 0 ≤ w e) (H : Finset (Fin n)) (i : ℤ) :
    let s : Fin n → Option ℤ := fun e => roundedLevel weightBase (w e)
    let d : MainMasks n := ⟨H, ∅, ∅, ∅, false⟩
    let U := trueGroup M d s i
    let Y := (positiveGreedy M s \ H).filter (fun e => s e = some i)
    densityThreshold ≤ (U.card : ℝ) →
      ((((2 : ℝ)^16)⁻¹ * Y.card - ((2 : ℝ)^23)⁻¹ * U.card) / (2 : ℝ)^100) ≤
        mainMean d (fun d' => (trueZ M hE d' s i : ℝ)) :=
  transfer_keys M hE (fun e => roundedLevel weightBase (w e)) H i

/-- Thin proof alias for the independent root-target specification. -/
theorem transfer_claim : TransferClaim := by
  intro n M hE w hw H i
  exact transfer M hE w hw H i

end MatroidProphet.SourceProof

end OAI
