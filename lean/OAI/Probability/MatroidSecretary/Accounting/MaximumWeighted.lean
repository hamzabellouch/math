import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Accounting.WeightedRewardModel

namespace OAI

/-! The literal rounded-payoff maximum-branch claim `eq:maximum` in setup.tex.
The observed input stays `w`; only the score attached to an accepted label is
rounded. This distinguishes the source assertion from a raw-payoff bound. -/

namespace MatroidProphet

open MeasureTheory Finset Set

lemma hiddenWorstScore_nonneg {n bits : ℕ} (A : HiddenRule n bits)
    (w score : Weights n) (hscore : ∀ e, 0 ≤ score e) (r : Seed bits) :
    0 ≤ hiddenWorstScore A w score r := by
  classical
  apply Finset.le_inf'
  intro π _
  exact Finset.sum_nonneg fun e _ => hscore e

namespace Maximum

variable {n bits : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [LinearOrder K]

/-- A singleton qualifier gives the actual singleton accepted set, not just its
raw reward. Therefore every nonnegative scoring of labels can use this event. -/
lemma maximumHidden_accepted_single_qualifier (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (r : Seed bits) (g : Fin n)
    (hg : g ∉ mask r)
    (ha : ∀ e, threshold M active mask r (fun f => key (w f)) (e, key (w e)) ↔ e = g)
    (π : ArrivalOrder n) :
    hiddenAcceptedThrough (maximumHidden M key hkey active mask) r w π n = {g} := by
  classical
  let A := maximumHidden M key hkey active mask
  have hsingle : accepted A.core r (observed A r w) w π = {g} := by
    apply firstRule_single_qualifier key hkey (threshold M active mask)
    intro e
    rw [threshold_congr_samples M active mask r
      (fun f => key (observed A r w f)) (fun f => key (w f))]
    · exact ha e
    · intro f hf
      simp [observed, A, maximumHidden, hf]
  change accepted A.core r (observed A r w) w π \ mask r = {g}
  rw [hsingle]
  exact Finset.sdiff_eq_self_of_disjoint (by simpa using hg)

/-- The all-order top-label guarantee remains valid for any nonnegative score
vector, while decisions still use exactly the original observations. -/
theorem maximum_expectation_top_score (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (w score : Weights n) (hscore : ∀ e, 0 ≤ score e) (g : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (key (w g)))
    (htop : ∀ f, M.Indep ({f} : Set (Fin n)) → active (key (w f)) → f ≠ g →
      higher (g, key (w g)) (f, key (w f))) :
    score g / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => hiddenWorstScore
        (maximumHidden M key hkey active (seedSet (bits := n))) w score (setSeed H)) := by
  classical
  let A := maximumHidden M key hkey active (seedSet (bits := n))
  let F : Finset (Fin n) → ℝ := fun H => hiddenWorstScore A w score (setSeed H)
  change score g / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ F
  have hF : ∀ H ⊆ Finset.univ, 0 ≤ F H :=
    fun H _ => hiddenWorstScore_nonneg A w score hscore (setSeed H)
  have hsuccess (H : Finset (Fin n)) (hgH : g ∉ H)
      (hqual : ∀ e, threshold M active seedSet (setSeed H)
        (fun f => key (w f)) (e, key (w e)) ↔ e = g) : score g ≤ F H := by
    apply Finset.le_inf'
    intro π _
    change score g ≤ ∑ e ∈ hiddenAcceptedThrough A (setSeed H) w π n, score e
    rw [maximumHidden_accepted_single_qualifier M key hkey active seedSet w
      (setSeed H) g (by simpa using hgH) hqual π, Finset.sum_singleton]
  let P : Finset (Fin n) := Finset.univ.filter fun f =>
    M.Indep ({f} : Set (Fin n)) ∧ active (key (w f)) ∧ f ≠ g
  by_cases hP : P.Nonempty
  · obtain ⟨h, hhP, hsecond⟩ := exists_top (fun f => key (w f)) P hP
    have hh := (Finset.mem_filter.mp hhP).2
    apply maximum_expectation_two Finset.univ g h (Finset.mem_univ _) (Finset.mem_univ _)
      (Ne.symm hh.2.2) F (score g) hF
    intro H _ hgH hhH
    apply hsuccess H hgH
    exact threshold_top_two M active seedSet (setSeed H) (fun f => key (w f))
      g h hg hag hh.1 hh.2.1 htop
      (fun f hf haf hfg hfh => hsecond f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf, haf, hfg⟩) hfh)
      (by simpa using hgH) (by simpa using hhH)
  · apply maximum_expectation_one Finset.univ g (Finset.mem_univ _) F (score g)
      (hscore g) hF
    intro H _ hgH
    apply hsuccess H hgH
    apply threshold_only_positive M active seedSet (setSeed H) (fun f => key (w f))
      g hg hag
    · intro f hf haf
      by_contra hfg
      exact hP ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf, haf, hfg⟩⟩
    · simpa using hgH

end Maximum

namespace SourceContracts

/-- The literal source `eq:maximum`: expected minimum *rounded* reward of
the maximum branch is at least one quarter of the largest rounded nonloop.
The observation mask is fair on every label and the minimum stays inside
the expectation. Empty, rank-zero, and all-zero instances are included. -/
theorem maximum_rounded {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (_hw : ∀ e, 0 ≤ w e) :
    maximumRounded M w / 4 ≤
      ∫ r, hiddenWorstScore (roundedMaximumHidden M (seedSet (bits := n)))
        w (fun e => roundedWeight weightBase (w e)) r
        ∂bernoulliSeedLaw (fun _ => (1 / 2 : ℝ))
          (fun _ => by norm_num) (fun _ => by norm_num) := by
  classical
  rw [integral_bernoulliSeedLaw]
  let score : Weights n := fun e => roundedWeight weightBase (w e)
  let A := roundedMaximumHidden M (seedSet (bits := n))
  let F := bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
    (fun H => hiddenWorstScore A w score (setSeed H))
  change maximumRounded M w / 4 ≤ F
  have hs : ∀ e, 0 ≤ score e :=
    fun e => roundedWeight_nonneg (by norm_num [weightBase]) (w e)
  have hF : 0 ≤ F := by
    apply bitsExpectation_nonneg _ (fun _ => by norm_num) (fun _ => by norm_num)
    intro H _
    exact hiddenWorstScore_nonneg A w score hs (setSeed H)
  have hlabel (e : Fin n) (he : M.Indep ({e} : Set (Fin n))) : score e ≤ 4 * F := by
    let a : Fin n → WithBot ℤ := fun f => Priority.asLevel (roundedLevel weightBase (w f))
    by_cases hea : a e = ⊥
    · have hz : score e = 0 := by
        change levelWeight weightBase (a e) = 0
        rw [hea]
        rfl
      rw [hz]
      exact mul_nonneg (by norm_num) hF
    · let P : Finset (Fin n) := Finset.univ.filter fun f =>
        M.Indep ({f} : Set (Fin n)) ∧ a f ≠ ⊥
      have heP : e ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ e, he, hea⟩
      obtain ⟨g, hgP, htop⟩ := Maximum.exists_top a P ⟨e, heP⟩
      have hg := (Finset.mem_filter.mp hgP).2
      have hwin : score g / 4 ≤ F :=
        Maximum.maximum_expectation_top_score M
          (fun x => Priority.asLevel (roundedLevel weightBase x))
          ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
          (fun x => x ≠ ⊥) w score hs g hg.1 hg.2
          (fun f hf haf hfg => htop f (Finset.mem_filter.mpr
            ⟨Finset.mem_univ f, hf, haf⟩) hfg)
      have hkey : a e ≤ a g := by
        by_cases heg : e = g
        · exact heg ▸ le_rfl
        · rcases htop e heP heg with hlt | ⟨heq, _⟩
          · exact hlt.le
          · exact heq.symm.le
      have hscore : score e ≤ score g :=
        levelWeight_mono (by norm_num [weightBase]) hkey
      linarith
  have hfour : maximumRounded M w ≤ 4 * F := by
    apply Finset.sup'_le
    intro o _
    cases o with
    | none => exact mul_nonneg (by norm_num) hF
    | some e =>
      change (if M.Indep ({e} : Set (Fin n)) then score e else 0) ≤ _
      split_ifs with he
      · exact hlabel e he
      · exact mul_nonneg (by norm_num) hF
  linarith

end SourceContracts
end MatroidProphet

end OAI
