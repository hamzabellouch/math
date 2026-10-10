import OAI.Probability.MatroidProphet.Maximum.Score

namespace OAI

namespace MatroidProphet.Maximum

open MeasureTheory Finset

lemma maximumHidden_mask_congr {n bits bits' : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (mask' : Seed bits' → Finset (Fin n))
    (r : Seed bits) (r' : Seed bits') (hm : mask r = mask' r')
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (maximumHidden M key hkey active mask) r w π t =
      hiddenAcceptedThrough (maximumHidden M key hkey active mask') r' w π t := by
  classical
  have hd (k : Fin n) :
      decisionAt (maximumRule M key hkey active mask) r
        (observed (maximumHidden M key hkey active mask) r w) w π k = true ↔
      decisionAt (maximumRule M key hkey active mask') r'
        (observed (maximumHidden M key hkey active mask') r' w) w π k = true := by
    unfold maximumRule
    rw [firstRule_decision, firstRule_decision]
    simp only [threshold, observed, maximumHidden, hm]
    rfl
  ext e
  change e ∈ acceptedThrough (maximumRule M key hkey active mask) r
      (observed (maximumHidden M key hkey active mask) r w) w π t \ mask r ↔
    e ∈ acceptedThrough (maximumRule M key hkey active mask') r'
      (observed (maximumHidden M key hkey active mask') r' w) w π t \ mask' r'
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  constructor
  · rintro ⟨he, hn⟩
    obtain ⟨_, ht, ha⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, (hd _).mp ha⟩,
      by simpa only [hm] using hn⟩
  · rintro ⟨he, hn⟩
    obtain ⟨_, ht, ha⟩ := Finset.mem_filter.mp he
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, (hd _).mpr ha⟩,
      by simpa only [hm] using hn⟩

lemma maximumHidden_worst_mask_congr {n bits bits' : ℕ} {K : Type*} [Countable K]
    [MeasurableSpace K] [MeasurableSingletonClass K] [LinearOrder K]
    (M : Matroid (Fin n)) (key : ℝ → K) (hkey : Measurable key) (active : K → Prop)
    (mask : Seed bits → Finset (Fin n)) (mask' : Seed bits' → Finset (Fin n))
    (r : Seed bits) (r' : Seed bits') (hm : mask r = mask' r') (w : Weights n) :
    hiddenWorstReward (maximumHidden M key hkey active mask) w r =
      hiddenWorstReward (maximumHidden M key hkey active mask') w r' := by
  classical
  unfold hiddenWorstReward
  congr 1
  funext π
  unfold hiddenReward
  rw [maximumHidden_mask_congr M key hkey active mask mask' r r' hm]

end MatroidProphet.Maximum

namespace MatroidProphet

noncomputable def maximumForMask {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (H : Finset (Fin n)) : ℝ :=
  hiddenWorstReward (roundedMaximumHidden M (seedSet (bits := n))) w (setSeed H)

lemma roundedMaximum_worst_mask {n bits : ℕ} (M : Matroid (Fin n))
    (mask : Seed bits → Finset (Fin n)) (r : Seed bits) (w : Weights n) :
    hiddenWorstReward (roundedMaximumHidden M mask) w r = maximumForMask M w (mask r) := by
  apply Maximum.maximumHidden_worst_mask_congr
  exact (seedSet_setSeed _).symm

lemma maximumPayoff_eq_masks {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    maximumPayoff M w = bitsExpectation (fun _ => (1/2 : ℝ)) Finset.univ (maximumForMask M w) := by
  exact integral_bernoulliSeedLaw _ _ _ _

end MatroidProphet

end OAI
