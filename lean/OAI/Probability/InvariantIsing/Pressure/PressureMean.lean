import OAI.Probability.InvariantIsing.Haar.MedianMean

namespace OAI

/-! Almost-sure concentration of the actual pressure about its expectation. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

/-- Deterministic reference obtained by removing the quadratic interaction. -/
def noninteractingPressure {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fieldEnergy c)

lemma rotatedPressure_zero {N : ℕ} (U : Rotation N) (c : Fin N → ℝ) :
    rotatedPressure (fun _ => 0) U c = noninteractingPressure c := by
  simp [rotatedPressure, rotatedEnergy, noninteractingPressure]

lemma abs_pressure_sub_noninteracting_le {N : ℕ} (hN : 0 < N)
    (eig c : Fin N → ℝ) (U : Rotation N) (K : ℝ) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedPressure eig U c - noninteractingPressure c| ≤ K / 2 := by
  simpa only [sub_zero, rotatedPressure_zero] using
    abs_rotatedPressure_sub_le hN eig (fun _ => 0) U c K (fun i => by simpa using heig i)

/-- Uniformly bounded spectra give almost-sure concentration about the mean,
for arbitrary deterministic fields and arbitrary dependence across dimensions. -/
theorem ae_pressure_sub_mean_tendsto_zero (hpub : HaarConcentrationInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : (n : ℕ) → Ω → SpecialOrthogonal (n + 3))
    (hU : ∀ n, Measurable (U n))
    (hHaar : ∀ n, (P.map (U n)).IsMulLeftInvariant)
    (eig c : (n : ℕ) → Fin (n + 3) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ n i, |eig n i| ≤ K) :
    ∀ᵐ ω ∂P, Tendsto (fun n =>
      rotatedPressure (eig n) (specialRotation (U n ω)) (c n) -
        ∫ η, rotatedPressure (eig n) (specialRotation (U n η)) (c n) ∂P)
      atTop (𝓝 0) := by
  let F : (n : ℕ) → SpecialOrthogonal (n + 3) → ℝ := fun n V =>
    rotatedPressure (eig n) (specialRotation V) (c n) - noninteractingPressure (c n)
  let f : ℕ → Ω → ℝ := fun n ω => F n (U n ω)
  have hFm (n : ℕ) : Measurable (F n) :=
    (measurable_rotatedPressure (eig n) (c n)).sub_const _
  have hfm (n : ℕ) : Measurable (f n) := (hFm n).comp (hU n)
  have hfb (n : ℕ) (ω : Ω) : |f n ω| ≤ K / 2 :=
    abs_pressure_sub_noninteracting_le (by omega) _ _ _ K (heig n)
  obtain ⟨C, a, hC, ha, hp⟩ := hpub
  have hm (n : ℕ) : ∃ m : ℝ,
      (1 / 2 : ℝ) ≤ P.real {ω | f n ω ≤ m} ∧
      (1 / 2 : ℝ) ≤ P.real {ω | m ≤ f n ω} ∧
      ∀ r : ℝ, 0 < r → P.real {ω | r ≤ |f n ω - m|} ≤
        C * Real.exp (-a * (n + 3 : ℝ) * r ^ 2 / K ^ 2) := by
    have hprob : IsProbabilityMeasure (P.map (U n)) :=
      (Measure.isProbabilityMeasure_map_iff (hU n).aemeasurable).mpr inferInstance
    have hLip : ∀ V W, |F n V - F n W| ≤ K * frobeniusDistance V W := by
      intro V W
      dsimp only [F]
      rw [sub_sub_sub_cancel_right]
      exact abs_rotatedPressure_sub_rotation_le (by omega) _ _ _ _ K hK.le (heig n)
    obtain ⟨m, hl, hu, ht⟩ := hp (n + 3) (by omega) (P.map (U n)) hprob
      (hHaar n) (F n) (hFm n) K hK hLip
    refine ⟨m, ?_, ?_, ?_⟩
    · simpa only [f, Set.preimage_ofPred_eq, measureReal_def, Measure.map_apply (hU n)
        (measurableSet_le (hFm n) measurable_const)] using hl
    · simpa only [f, Set.preimage_ofPred_eq, measureReal_def, Measure.map_apply (hU n)
        (measurableSet_le measurable_const (hFm n))] using hu
    · intro r hr
      simpa only [f, Set.preimage_ofPred_eq, measureReal_def, Measure.map_apply (hU n)
        (measurableSet_le measurable_const ((hFm n).sub_const m).abs),
        Nat.cast_add, Nat.cast_ofNat] using ht r hr
  choose m hl hu ht using hm
  have htail : ∀ r : ℝ, 0 < r → ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
      ∀ n, P.real {ω | r ≤ |f n ω - m n|} ≤ C * Real.exp (-a * (n : ℝ)) := by
    intro r hr
    refine ⟨C, a * r ^ 2 / K ^ 2, hC.le, by positivity, ?_⟩
    intro n
    refine (ht n r hr).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le)
    have hnonneg : 0 ≤ a * r ^ 2 / K ^ 2 := by positivity
    calc
      -a * ((n : ℝ) + 3) * r ^ 2 / K ^ 2 =
          -(a * r ^ 2 / K ^ 2) * ((n : ℝ) + 3) := by ring
      _ ≤ -(a * r ^ 2 / K ^ 2) * (n : ℝ) :=
        mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hnonneg)
  have hmean := tendsto_mean_sub_median_zero P f hfm m (K / 2) (by positivity)
    hfb hl hu htail
  have hae := ae_tendsto_zero_of_exponential_tail P (fun n ω => f n ω - m n) htail
  have hfi (n : ℕ) : Integrable (f n) P :=
    (integrable_const (K / 2)).mono' (hfm n).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hfb n ω)
  filter_upwards [hae] with ω hω
  have hresult := hω.sub hmean
  have he (n : ℕ) :
      f n ω - m n - ((∫ η, f n η ∂P) - m n) =
        rotatedPressure (eig n) (specialRotation (U n ω)) (c n) -
          ∫ η, rotatedPressure (eig n) (specialRotation (U n η)) (c n) ∂P := by
    have hadd := integral_add (hfi n) (integrable_const (noninteractingPressure (c n)))
    have heq : (fun η => f n η + noninteractingPressure (c n)) =
        (fun η => rotatedPressure (eig n) (specialRotation (U n η)) (c n)) := by
      funext η
      simp [f, F]
    rw [heq] at hadd
    simp only [integral_const, probReal_univ, one_smul] at hadd
    dsimp only [f, F]
    linarith
  simpa only [he, sub_self] using hresult

end InvariantIsing

end

end OAI
