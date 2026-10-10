import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelSphere

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression

def uniformChordSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | dist (L.estimate z.1 z.2.1 z.2.2).val z.1.val ≤ ε}
end MemoryPrecision
namespace MemoryPrecision
open NoiselessRegression
lemma real_route_cap_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N} (hδ : ∀ n j, Measurable (δ n j))
    (y : Fin N → Space d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) (k : ℕ) (j : Fin N) :
    ((SpherePrior d).prod (Measure.pi (fun _ : Fin k => stdGaussian (Space d))))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d N ^ BlockCount k (d/8)) := by
  let : NeZero d := ⟨by omega⟩
  let : NeZero N := ⟨by omega⟩
  let : IsProbabilityMeasure (SpherePrior d) :=
    (show IsProbabilityMeasure (sphereLaw (E := Space d)) from inferInstance)
  let w : ℕ → Fin N → Space d → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have he (s : Space d) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → Space d, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian (Space d)) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set (Sphere d × (Fin k → Space d)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((SpherePrior d).prod _) S ≤ _
  rw [← one_mul (((SpherePrior d).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Sphere d,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian (Space d))) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  exact real_continuation_cap_integral hd hN hδ (fun _ => y) hε hαlo hαhi 0 k j

lemma real_prefix_route_cap_bound {d N : ℕ} (hd : 16 ≤ d) (hN : 1 ≤ N)
    {δ : ℕ → Fin N → (Space d × ℝ) → Fin N} (hδ : ∀ n j, Measurable (δ n j))
    (y : Fin N → Space d) {ε α : ℝ} (hε : 0 < ε)
    (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) {k T : ℕ} (hk : k ≤ T) (j : Fin N) :
    ((SpherePrior d).prod (Measure.pi (fun _ : Fin T => stdGaussian (Space d))))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d N ^ BlockCount T (d/8)) := by
  let : NeZero d := ⟨by omega⟩
  let : NeZero N := ⟨by omega⟩
  let : IsProbabilityMeasure (SpherePrior d) :=
    (show IsProbabilityMeasure (sphereLaw (E := Space d)) from inferInstance)
  have hp := (MeasurePreserving.id (SpherePrior d)).prod
    (measurePreserving_pi_prefix (stdGaussian (Space d)) hk)
  have hs : MeasurableSet
      {z : Sphere d × (Fin k → Space d) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  apply (real_route_cap_bound hd hN hδ y hε hαlo hαhi k j).trans
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (realStep_one d hN) (blockCount_mono hk)) (by positivity))

open NoiselessRegression.Learner

lemma frozen_chord_real_bound {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (ω : Ω) (hd : 16 ≤ d)
    (htrans : ∀ t j, AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε} ≤
      (T+1 : ℝ≥0∞) * ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M) ^ BlockCount T (d/8)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let δ : ℕ → State M → (Vector d × ℝ) → State M := fun t j => (htrans t j).mk _
  have hδ (t : ℕ) (j : State M) : Measurable (δ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      (L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫)).2 = δ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using (show 3 ≤ d by omega)) i).ae (htrans t j).ae_eq_mk
  let S : Fin (T+1) → Set (UnitSphere d × Samples d T) := fun t =>
    {z | dist z.1.val (L.output t ω (streamRoute δ 0 t (L.initialChoice ω).2
      ((fun i => z.2 (Fin.castLE (by omega) i)),fun i => ⟪z.1.val,z.2 (Fin.castLE (by omega) i)⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε}
      ≤ᵐ[μ] ⋃ t, S t := by
    filter_upwards [hgood] with z hz
    intro hs
    rcases L.terminal_forced_witness z.1 ω z.2 with ⟨t,ht,he⟩
    have hf : L.forcedRun z.1 ω z.2 t = streamRoute δ 0 t (L.initialChoice ω).2
        ((fun i => z.2 (Fin.castLE ht i)),fun i => ⟪z.1.val,z.2 (Fin.castLE ht i)⟫) := by
      rw [L.forcedRun_eq_route z.1 ω z.2 ht]
      exact streamRoute_congr _ _ 0 t _ _ _ (fun n j i => hz n j (Fin.castLE ht i))
    refine Set.mem_iUnion.mpr ⟨⟨t,by omega⟩, ?_⟩
    change dist z.1.val (L.output t ω _) ≤ ε
    change dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε at hs
    simpa only [estimate, he, hf] using hs
  let B : ℝ≥0∞ := ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M) ^ BlockCount T (d/8))
  have hb (t : Fin (T+1)) : μ (S t) ≤ B := by
    simpa only [B, μ, S, uniformSphere, SpherePrior, MemoryPrecision.Kernel.UniformSphere,
      sampleLaw] using
      real_prefix_route_cap_bound (N := 2^M) hd (one_le_pow₀ (by norm_num)) hδ (fun j => (L.output t ω j).val) hε
        hαlo hαhi (by omega : (t : ℕ) ≤ T) (L.initialChoice ω).2
  calc
    _ ≤ μ (⋃ t, S t) := measure_mono_ae hmono
    _ ≤ ∑' t, μ (S t) := measure_iUnion_le S
    _ ≤ ∑' _ : Fin (T+1), B := ENNReal.tsum_le_tsum hb
    _ = _ := by simp [B, tsum_fintype, nsmul_eq_mul, mul_assoc]

lemma chord_real_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 16 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {α : ℝ} (hαlo : ((d:ℝ)-1)/2 ≤ α) (hαhi : α ≤ (d:ℝ)/2) :
    uniformChordSuccess L ρ ε ≤
      (T+1 : ℝ≥0∞) * ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M) ^ BlockCount T (d/8)) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (fun obs => (L.transition t ω j obs).2) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    filter_upwards [ae_fiber_aemeasurable (hL.transition t j).prod_swap] with ω hω
    exact measurable_snd.comp_aemeasurable hω
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    dist (L.estimate z.1 z.2.1 z.2.2).val z.1.val ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    nullMeasurableSet_le
      ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).dist
        (measurable_subtype_coe.comp measurable_fst).aemeasurable) aemeasurable_const
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (T+1 : ℝ≥0∞) * ENNReal.ofReal ((3*4^d:ℝ)*ε^((d:ℝ)-1-α) * RealStep d (2^M) ^ BlockCount T (d/8)))
    (by
      filter_upwards [hω] with ω hω
      change ((uniformSphere d).prod (sampleLaw d T))
        {z | dist (L.estimate z.1 ω z.2).val z.1.val ≤ ε} ≤ _
      simpa only [dist_comm] using frozen_chord_real_bound L ω hd hω hε hαlo hαhi)
  simpa only [he, measure_univ, mul_one, S, uniformChordSuccess] using hb

end MemoryPrecision


end

end OAI
