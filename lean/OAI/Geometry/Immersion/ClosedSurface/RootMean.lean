import OAI.Geometry.Immersion.ClosedSurface.RealBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def positivePair : Set (Fin 2 → ℝ) := {p | 0 < p 0 ∧ 0 < p 1}
def rootDifferenceCoefficient (p : Fin 2 → ℝ) : ℝ :=
  (Real.sqrt (p 0) + Real.sqrt (p 1))⁻¹

lemma positivePair_isOpen : IsOpen positivePair :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt continuous_const (continuous_apply 1))

lemma contDiffOn_rootDifferenceCoefficient :
    ContDiffOn ℝ ∞ rootDifferenceCoefficient positivePair := by
  have h0 : ContDiffOn ℝ ∞ (fun p : Fin 2 → ℝ => p 0) positivePair :=
    (contDiff_apply ℝ ℝ (0 : Fin 2)).contDiffOn
  have h1 : ContDiffOn ℝ ∞ (fun p : Fin 2 → ℝ => p 1) positivePair :=
    (contDiff_apply ℝ ℝ (1 : Fin 2)).contDiffOn
  have hs0 := h0.sqrt (fun p (hp : p ∈ positivePair) => ne_of_gt hp.1)
  have hs1 := h1.sqrt (fun p (hp : p ∈ positivePair) => ne_of_gt hp.2)
  exact (hs0.add hs1).inv (fun p hp => ne_of_gt
    (add_pos (Real.sqrt_pos.2 hp.1) (Real.sqrt_pos.2 hp.2)))

lemma sqrt_difference {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt u - Real.sqrt v = (u - v) * rootDifferenceCoefficient ![u, v] := by
  have hh : Real.sqrt u + Real.sqrt v ≠ 0 := ne_of_gt
    (add_pos (Real.sqrt_pos.2 hu) (Real.sqrt_pos.2 hv))
  dsimp [rootDifferenceCoefficient]
  rw [← div_eq_mul_inv]
  apply (eq_div_iff hh).2
  nlinarith [Real.sq_sqrt hu.le, Real.sq_sqrt hv.le]

lemma compact_root_bound {U : Set E} (hU : UniqueDiffOn ℝ U)
    {r R : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (u : E → ℝ) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiffOn ℝ ∞ u U → MapsTo u U (Icc r R) → WeightedBound U s m C u →
      WeightedBound U s m ((m.factorial : ℝ) * D * C ^ m) (fun p => Real.sqrt (u p)) := by
  have hroot : ContDiffOn ℝ ∞ Real.sqrt (Ioi (0 : ℝ)) :=
    contDiffOn_id.sqrt (fun p hp => ne_of_gt hp)
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU isOpen_Ioi.uniqueDiffOn
    (isCompact_Icc : IsCompact (Icc r R)) (fun p hp => hr.trans_le hp.1) hroot m
  exact ⟨D, hD, hbD⟩

lemma compact_root_difference_bound {U : Set E} (hU : UniqueDiffOn ℝ U)
    {r R : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (u v : E → ℝ) (s C A : ℝ), 0 < s → 1 ≤ C → 0 ≤ A →
      ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      MapsTo u U (Icc r R) → MapsTo v U (Icc r R) →
      WeightedBound U s m C u → WeightedBound U s m C v →
      WeightedBound U s m A (fun p => u p - v p) →
      WeightedBound U s m (2 ^ m * A * ((m.factorial : ℝ) * D * C ^ m))
        (fun p => Real.sqrt (u p) - Real.sqrt (v p)) := by
  let K : Set (Fin 2 → ℝ) := Icc (fun _ => r) (fun _ => R)
  have hKV : K ⊆ positivePair := by
    intro p hp
    exact ⟨hr.trans_le (hp.1 0), hr.trans_le (hp.1 1)⟩
  obtain ⟨D, hD, hbD⟩ := smooth_compact_weighted_bound hU positivePair_isOpen.uniqueDiffOn
    (isCompact_Icc : IsCompact K) hKV contDiffOn_rootDifferenceCoefficient m
  refine ⟨D, hD, ?_⟩
  intro u v s C A hs hC hA hu hv hru hrv hbu hbv hbuv
  let f : E → Fin 2 → ℝ := fun p => ![u p, v p]
  have hf : ContDiffOn ℝ ∞ f U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i <;> simpa [f] using (by assumption : ContDiffOn ℝ ∞ _ U)
  have hfk : MapsTo f U K := by
    intro p hp
    constructor <;> intro i <;> fin_cases i <;>
      simp only [f]
    · exact (hru hp).1
    · exact (hrv hp).1
    · exact (hru hp).2
    · exact (hrv hp).2
  have hbf : WeightedBound U s m C f := by
    apply WeightedBound.pi hU hs (le_trans zero_le_one hC)
    · intro i; exact contDiffOn_pi.mp hf i
    · intro i; fin_cases i
      · exact hbu
      · exact hbv
  have hbCoef := hbD f s C hs hC hf hfk hbf
  have hc : ContDiffOn ℝ ∞ (rootDifferenceCoefficient ∘ f) U :=
    contDiffOn_rootDifferenceCoefficient.comp hf (fun p hp => hKV (hfk hp))
  apply (hbuv.real_mul hU hs.le hA (by positivity) (hu.sub hv) hc hbCoef).congr
  intro p hp
  exact sqrt_difference (hr.trans_le (hru hp).1) (hr.trans_le (hrv hp).1)

end ClosedSurfaceR4.RootMean

namespace ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def phaseAmplitude (ψ u : E → ℝ) : E → ℝ := fun p => ψ p * Real.sqrt (u p)

lemma contDiffOn_phaseAmplitude {U : Set E} {ψ u : E → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ U) (hu : ContDiffOn ℝ ∞ u U)
    (hpos : ∀ p ∈ U, 0 < u p) : ContDiffOn ℝ ∞ (phaseAmplitude ψ u) U :=
  hψ.mul (hu.sqrt (fun p hp => ne_of_gt (hpos p hp)))



lemma compact_amplitude_bounds {U : Set E} (hU : UniqueDiffOn ℝ U)
    {r R C P : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hP : 0 ≤ P) (m : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (s A : ℝ) (ψ u v : E → ℝ), 0 < s → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      MapsTo u U (Icc r R) → MapsTo v U (Icc r R) →
      WeightedBound U s m P ψ → WeightedBound U s m C u → WeightedBound U s m C v →
      WeightedBound U s m A (fun p => u p - v p) →
      WeightedBound U s m K (phaseAmplitude ψ u) ∧
      WeightedBound U s m K (phaseAmplitude ψ v) ∧
      WeightedBound U s m (K * A) (fun p => phaseAmplitude ψ u p - phaseAmplitude ψ v p) := by
  obtain ⟨D0, hD0, hb0⟩ := compact_root_bound (R := R) hU hr m
  obtain ⟨D1, hD1, hb1⟩ := compact_root_difference_bound (R := R) hU hr m
  let B0 := (m.factorial : ℝ) * D0 * C ^ m
  let B1 := (m.factorial : ℝ) * D1 * C ^ m
  let K := max 1 (max (2 ^ m * P * B0) (2 ^ m * P * (2 ^ m * B1)))
  have hK0 : 2 ^ m * P * B0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK1 : 2 ^ m * P * (2 ^ m * B1) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro s A ψ u v hs hA hψ hu hv hru hrv hbψ hbu hbv hbuv
  have hpu : ∀ p ∈ U, u p ≠ 0 := fun p hp => ne_of_gt (hr.trans_le (hru hp).1)
  have hpv : ∀ p ∈ U, v p ≠ 0 := fun p hp => ne_of_gt (hr.trans_le (hrv hp).1)
  have hrootu := hb0 u s C hs hC hu hru hbu
  have hrootv := hb0 v s C hs hC hv hrv hbv
  have hrootd := hb1 u v s C A hs hC hA hu hv hru hrv hbu hbv hbuv
  have hba := hbψ.real_mul hU hs.le hP (by positivity) hψ (hu.sqrt hpu) hrootu
  have hbb := hbψ.real_mul hU hs.le hP (by positivity) hψ (hv.sqrt hpv) hrootv
  refine ⟨hba.mono_const hK0, hbb.mono_const hK0, ?_⟩
  have hbd := hbψ.real_mul hU hs.le hP (by positivity) hψ
    ((hu.sqrt hpu).sub (hv.sqrt hpv)) hrootd
  have hbound : 2 ^ m * P * (2 ^ m * A * B1) ≤ K * A := by
    calc
      _ = (2 ^ m * P * (2 ^ m * B1)) * A := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hA
  apply (hbd.mono_const hbound).congr
  intro p hp
  dsimp [phaseAmplitude]
  ring

end ClosedSurfaceR4.RootMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.RootMean
open Set




theorem actual_mean_amplitude_difference {U : Set Base} (hU : IsOpen U)
    {r R C P : ℝ} (hr : 0 < r) (hC : 1 ≤ C) (hP : 0 ≤ P) (q m : ℕ) :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ (F : RField 4) (δ τ s K B A : ℝ) (ψ u v : Base → ℝ),
      ContDiff ℝ ∞ F → RealModeDomain F U → 0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      0 ≤ K → 0 ≤ B → 0 ≤ A →
      ContDiffOn ℝ ∞ ψ U → ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U →
      MapsTo u U (Icc r R) → MapsTo v U (Icc r R) →
      ReconstructionCoefficientBound (fun p => complexify (F p)) U s (m + q + 2) K →
      WeightedBound U s (m + q + 2) B (freeNormal F) →
      WeightedBound U s (m + q + 2) P ψ →
      WeightedBound U s (m + q + 2) C u → WeightedBound U s (m + q + 2) C v →
      WeightedBound U s (m + q + 2) A (fun p => u p - v p) →
      ∀ (w z : Base), ‖w‖ ≤ 1 → ‖z‖ ≤ 1 →
      WeightedBound U s m (2 * meanErrorConstant 4 m K q *
        (Real.sqrt 2 * 2 ^ (m + q + 2) * B) ^ 2 * A0 ^ 2 * A * (τ / s))
        (fun p => normalizedMeanError δ τ F (phaseAmplitude ψ u) q w z p -
          normalizedMeanError δ τ F (phaseAmplitude ψ v) q w z p) := by
  obtain ⟨A0, hA0, hb⟩ := compact_amplitude_bounds (R := R) hU.uniqueDiffOn hr hC hP (m + q + 2)
  refine ⟨A0, hA0, ?_⟩
  intro F δ τ s K B A ψ u v hF h hδ hτ hs hτs hs1 hK hB hA hψ hu hv hru hrv hc hbN hbψ hbu hbv hbuv w z hw hz
  obtain ⟨hba, hbb, hbd⟩ := hb s A ψ u v hs hA hψ hu hv hru hrv hbψ hbu hbv hbuv
  have hsa := contDiffOn_phaseAmplitude hψ hu (fun p hp => hr.trans_le (hru hp).1)
  have hsb := contDiffOn_phaseAmplitude hψ hv (fun p hp => hr.trans_le (hrv hp).1)
  have hh := weighted_normalizedMeanError_difference hF h hδ hτ hs hτs hs1 hK
    (le_trans zero_le_one hA0) (mul_nonneg (le_trans zero_le_one hA0) hA) hB hsa hsb q m
    hc hba hbb hbd hbN w z hw hz
  convert hh using 1
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
