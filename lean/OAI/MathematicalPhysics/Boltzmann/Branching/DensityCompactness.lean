import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTailRegions

namespace OAI

/-! # Uniform integrability of the actual one-particle densities -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.Compactness
open BoltzmannNonuniqueness.AnnularEnvelope

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem outer_density_uniformIntegrable [IsFiniteMeasure μ] {q A : ℝ}
    (hq : q < 2) (hA : 0 ≤ A) {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    {S : Set X} (hS : MeasurableSet S)
    (hdom : ∀ n, ∀ᵐ x ∂μ, ∀ᵐ v : Velocity, x ∉ S → f n (x,v) ≤ A*H q v) :
    UniformIntegrable (fun n => outerCutoff S (f n)) 1 (μ.prod (volume : Measure Velocity)) := by
  have hi : Integrable (fun p : X × Velocity => A*H q p.2) (μ.prod volume) :=
    ((integrable_H hq).const_mul A).comp_snd μ
  apply uniformIntegrable_mono_nonneg
    (uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hi))
    (fun n => ((hfm n).indicator (hS.compl.preimage measurable_fst)).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun p => indicator_nonneg (fun p _ => hf n p) p))
  intro n
  have hHm : Measurable (fun p : X × Velocity => A*H q p.2) := by
    unfold H singularity
    fun_prop
  have hmP : MeasurableSet {p : X × Velocity | p.1 ∉ S → f n p ≤ A*H q p.2} := by
    convert (hS.preimage measurable_fst).union (measurableSet_le (hfm n) hHm) using 1
    ext p
    simp only [mem_ofPred_eq,mem_union,mem_preimage,not_not,imp_iff_not_or]
  filter_upwards [(Measure.ae_prod_iff_ae_ae hmP).mpr (hdom n)] with p hp
  change outerCutoff S (f n) p ≤ A*H q p.2
  by_cases hs : p.1 ∈ S
  · rw [outerCutoff,indicator_of_notMem (show p ∉ Prod.fst ⁻¹' Sᶜ from fun h => h hs)]
    exact mul_nonneg hA (H_nonneg q p.2)
  · rw [outerCutoff,indicator_of_mem (show p ∈ Prod.fst ⁻¹' Sᶜ from hs)]
    exact hp hs

theorem torus_common_integrable {s₀ η T A B : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Integrable (fun u => commonMoment s₀ η A B (torusChart u)) (timePositionVolume T) := by
  have hi := (integrable_const (1 : ℝ) (μ := timePositionVolume T)).add
    (torus_common_square_integrable hs₀ hη hηmax hT A B)
  apply hi.mono' ((commonMoment_measurable s₀ η A B).comp torusChart_measurable).aestronglyMeasurable
  filter_upwards [] with u
  dsimp only [Function.comp_apply,Pi.add_apply]
  rw [Real.norm_of_nonneg (commonMoment_nonneg hA hB s₀ η (torusChart u))]
  nlinarith [sq_nonneg (commonMoment s₀ η A B (torusChart u)-1)]

theorem annular_density_uniformIntegrable {s₀ η T q A B : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T)
    (hq : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f : ℕ → (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hmoment : ∀ n, ∀ᵐ u ∂timePositionVolume T,
      VelocityMoment.moment (fun v => f n (u,v)) ≤
        ENNReal.ofReal (commonMoment s₀ η A B (torusChart u)))
    (houter : ∀ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      ∀ᵐ u ∂timePositionVolume T, ∀ᵐ v : Velocity,
        u ∉ torusTail s₀ η J → f n (u,v) ≤ D*H q v) :
    UniformIntegrable f 1 ((timePositionVolume T).prod (volume : Measure Velocity)) := by
  apply uniformIntegrable_of_spatial_cutoffs hfm hf (torusTail_measurable s₀ η)
  · intro n
    filter_upwards [hmoment n] with u hu
    apply le_trans (lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_left (hf n (u,v)) (VelocityMoment.weight_one_le v)))) hu
  · intro J
    obtain ⟨D,hD,hDom⟩ := houter J
    exact outer_density_uniformIntegrable hq hD hfm hf (torusTail_measurable s₀ η J) hDom
  · exact torus_tail_lintegral_tendsto hs₀.le hη.le
      (torus_common_integrable hs₀ hη hηmax hT hA hB)
      (fun u => commonMoment_nonneg hA hB s₀ η (torusChart u))

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
