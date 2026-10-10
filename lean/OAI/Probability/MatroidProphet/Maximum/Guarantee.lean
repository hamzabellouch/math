import OAI.Probability.MatroidProphet.Maximum.Probability
import OAI.Probability.MatroidProphet.SeedLaw
import OAI.Probability.MatroidProphet.Simulation

namespace OAI

namespace MatroidProphet.Maximum

open MeasureTheory Finset Set

variable {n : ℕ} {K : Type*} [Countable K] [MeasurableSpace K]
  [MeasurableSingletonClass K] [LinearOrder K]

lemma le_hiddenWorstReward {bits : ℕ} (A : HiddenRule n bits) (w : Weights n)
    (r : Seed bits) (c : ℝ) (h : ∀ π, c ≤ hiddenReward A r w π) :
    c ≤ hiddenWorstReward A w r := by
  classical
  apply Finset.le_inf'
  intro π _
  exact h π

theorem maximum_integral_top (M : Matroid (Fin n))
    (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (g : Fin n)
    (hg : M.Indep ({g} : Set (Fin n))) (hag : active (key (w g)))
    (htop : ∀ f, M.Indep ({f} : Set (Fin n)) → active (key (w f)) → f ≠ g →
      higher (g, key (w g)) (f, key (w f))) :
    w g / 4 ≤ ∫ r, hiddenWorstReward
      (maximumHidden M key hkey active (seedSet (bits := n))) w r
      ∂bernoulliSeedLaw (fun _ => (1 / 2 : ℝ))
        (fun _ => by norm_num) (fun _ => by norm_num) := by
  classical
  let A := maximumHidden M key hkey active (seedSet (bits := n))
  let F : Finset (Fin n) → ℝ := fun H => hiddenWorstReward A w (setSeed H)
  rw [integral_bernoulliSeedLaw]
  change w g / 4 ≤ bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ F
  have hF : ∀ H ⊆ Finset.univ, 0 ≤ F H :=
    fun H _ => hiddenWorstReward_nonneg A w hw (setSeed H)
  let P : Finset (Fin n) := Finset.univ.filter fun f =>
    M.Indep ({f} : Set (Fin n)) ∧ active (key (w f)) ∧ f ≠ g
  by_cases hP : P.Nonempty
  · obtain ⟨h, hhP, hsecond⟩ := exists_top (fun f => key (w f)) P hP
    have hh := (Finset.mem_filter.mp hhP).2
    apply maximum_expectation_two Finset.univ g h (Finset.mem_univ _) (Finset.mem_univ _)
      (Ne.symm hh.2.2) F (w g) hF
    intro H _ hgH hhH
    apply le_hiddenWorstReward
    intro π
    have hqual := threshold_top_two M active (seedSet (bits := n)) (setSeed H)
      (fun f => key (w f)) g h hg hag hh.1 hh.2.1 htop
      (fun f hf haf hfg hfh => hsecond f (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, haf, hfg⟩) hfh)
      (by simpa using hgH) (by simpa using hhH)
    exact (maximumHidden_single_qualifier M key hkey active seedSet w (setSeed H) g
      (by simpa using hgH) hqual π).symm.le
  · apply maximum_expectation_one Finset.univ g (Finset.mem_univ _) F (w g) (hw g) hF
    intro H _ hgH
    apply le_hiddenWorstReward
    intro π
    have honly : ∀ f, M.Indep ({f} : Set (Fin n)) → active (key (w f)) → f = g := by
      intro f hf haf
      by_contra hfg
      exact hP ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, haf, hfg⟩⟩
    have hqual := threshold_only_positive M active (seedSet (bits := n)) (setSeed H)
      (fun f => key (w f)) g hg hag honly (by simpa using hgH)
    exact (maximumHidden_single_qualifier M key hkey active seedSet w (setSeed H) g
      (by simpa using hgH) hqual π).symm.le

end MatroidProphet.Maximum

end OAI
