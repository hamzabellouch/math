import OAI.Probability.FreeIsing.Martingales.ContinuousSubsequence
import OAI.Probability.FreeIsing.Martingales.PredictableVersion

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

def repair {Ω : Type*} (u : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => sample u n t ω)

theorem repair_isStronglyPredictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) : IsStronglyPredictable F (repair u) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact StronglyMeasurable.limUnder (fun n => sample_isStronglyPredictable hu n)

theorem repair_eq_of_continuousOn {Ω : Type*} {u : ℝ≥0 → Ω → ℝ}
    {T : ℝ≥0} {ω : Ω} (hc : ContinuousOn (fun t => u t ω) (Iic T))
    {t : ℝ≥0} (ht : t ≤ T) : repair u t ω = u t ω := by
  apply Filter.Tendsto.limUnder_eq
  apply (hc t ht).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_left t, Filter.Eventually.of_forall
    (fun n => (left_le n t).trans ht)⟩

end Problem367.PredictableMesh

namespace Problem367.MartingaleSquareMaximal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}

theorem exists_predictable_continuous_subsequence_of_terminal_L2_cauchy
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω)) (T : ℝ≥0)
    (hC : CauchySeq (fun n => (h2 n T).toLp (M n T))) :
    ∃ (v : ℕ → ℕ) (L : ℝ≥0 → Ω → ℝ), StrictMono v ∧
      IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => L t ω) (Iic T)) ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T,
        Tendsto (fun n => M (v n) t ω) atTop (𝓝 (L t ω))) := by
  obtain ⟨v, hv, hlim⟩ :=
    exists_continuous_subsequence_of_terminal_L2_cauchy hM h2 hc T hC
  let R : ℝ≥0 → Ω → ℝ := fun t ω => limUnder atTop (fun n => M (v n) t ω)
  have hR : StronglyAdapted F R := fun t => by
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder (fun n => (hM (v n)).stronglyMeasurable t)
  have hpath : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T) ∧
      ∀ t ≤ T, Tendsto (fun n => M (v n) t ω) atTop (𝓝 (R t ω)) := by
    filter_upwards [hlim] with ω hω
    obtain ⟨f, hf⟩ := hω
    have heq (t : Iic T) : R t ω = f t := (hf t).limUnder_eq
    constructor
    · rw [continuousOn_iff_continuous_domRestrict]
      exact f.continuous.congr (fun t => (heq t).symm)
    · intro t ht
      simpa only [heq ⟨t, ht⟩] using hf ⟨t, ht⟩
  refine ⟨v, PredictableMesh.repair R, hv,
    PredictableMesh.repair_isStronglyPredictable hR, ?_, ?_⟩
  · filter_upwards [hpath] with ω hω
    exact hω.1.congr (fun t ht => PredictableMesh.repair_eq_of_continuousOn hω.1 ht)
  · filter_upwards [hpath] with ω hω
    intro t ht
    rw [PredictableMesh.repair_eq_of_continuousOn hω.1 ht]
    exact hω.2 t ht

end Problem367.MartingaleSquareMaximal

end

end OAI
