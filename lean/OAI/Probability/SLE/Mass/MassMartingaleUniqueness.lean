import OAI.Probability.SLE.Mass.MassUniquenessMesh
import OAI.Probability.SLE.Mass.MassMartingaleTesting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.DenseEmbedding

namespace OAI

/-! Uniqueness of a continuous mass process from its integrable increasing
variation and martingale difference. No second moment is imposed on a competing
mass construction. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (A B : ℝ≥0 → Ω → ℝ)

/-- A continuous martingale which is the difference of two increasing processes
starting at zero vanishes, using only integrability of the two endpoint masses. -/
theorem increasing_mass_martingale_eq_at
    (hM : Martingale (fun t ω => A t ω-B t ω) ℱ P)
    (hA : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hB : ∀ᵐ ω ∂P, Monotone (fun t => B t ω))
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0)
    (T : ℝ≥0) (hAI : Integrable (A T) P) (hBI : Integrable (B T) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => A t ω-B t ω) (Icc 0 T)) :
    A T =ᵐ[P] B T := by
  let M : ℝ≥0 → Ω → ℝ := fun t ω => A t ω-B t ω
  let X : ℕ → Ω → ℝ := fun n ω =>
    massPartitionRemainder (fun i => M (massTimeMesh T n i) ω) (n+1)
  have hXint (n : ℕ) : Integrable (X n) P := by
    have hsum : Integrable (fun ω => ∑ i ∈ Finset.range (n+1),
        massSeparationSlope (M (massTimeMesh T n i) ω)*
          (M (massTimeMesh T n (i+1)) ω-M (massTimeMesh T n i) ω)) P :=
      integrable_finsetSum _ (fun i _ =>
        martingale_mass_weighted_increment_integrable hM _ _)
    exact ((martingale_mass_test_integrable hM _).sub
      (martingale_mass_test_integrable hM _)).sub hsum
  have hXmean (n : ℕ) : (∫ ω, X n ω ∂P) = ∫ ω, massSeparationTest (M T ω) ∂P := by
    have hsum (i : ℕ) := martingale_mass_weighted_increment_integrable hM
      (massTimeMesh T n i) (massTimeMesh T n (i+1))
    change (∫ ω, massSeparationTest (M (massTimeMesh T n (n+1)) ω)-
      massSeparationTest (M (massTimeMesh T n 0) ω)-
        ∑ i ∈ Finset.range (n+1), massSeparationSlope (M (massTimeMesh T n i) ω)*
          (M (massTimeMesh T n (i+1)) ω-M (massTimeMesh T n i) ω) ∂P) = _
    rw [massTimeMesh_end,massTimeMesh_zero,
      integral_sub (f := fun ω => massSeparationTest (M T ω)-massSeparationTest (M 0 ω))
        (g := fun ω => ∑ i ∈ Finset.range (n+1), massSeparationSlope (M (massTimeMesh T n i) ω)*
          (M (massTimeMesh T n (i+1)) ω-M (massTimeMesh T n i) ω))
        ((martingale_mass_test_integrable hM T).sub
        (martingale_mass_test_integrable hM 0)) (integrable_finsetSum _ (fun i _ => hsum i)),
      integral_sub (f := fun ω => massSeparationTest (M T ω))
        (g := fun ω => massSeparationTest (M 0 ω))
        (martingale_mass_test_integrable hM T) (martingale_mass_test_integrable hM 0),
      integral_finsetSum _ (fun i _ => hsum i)]
    have hzero : (fun ω => massSeparationTest (M 0 ω)) =ᵐ[P] 0 := by
      filter_upwards [hA0,hB0] with ω ha hb
      simp only [M,ha,hb,Pi.zero_apply,sub_self,massSeparationTest_zero]
    have hmeans : (∑ i ∈ Finset.range (n+1), ∫ ω,
        massSeparationSlope (M (massTimeMesh T n i) ω)*
          (M (massTimeMesh T n (i+1)) ω-M (massTimeMesh T n i) ω) ∂P) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact martingale_mass_weighted_increment_mean hM (massTimeMesh_mono T n (Nat.le_succ i))
    simp only [M] at hmeans
    rw [integral_congr_ae hzero,hmeans]
    simp
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖X n ω‖ ≤ 4*(A T ω+B T ω) := by
    filter_upwards [hA,hB,hA0,hB0] with ω ha hb ha0 hb0
    calc
      _ ≤ 4*∑ i ∈ Finset.range (n+1),
          |M (massTimeMesh T n (i+1)) ω-M (massTimeMesh T n i) ω| := by
        simpa only [X,Real.norm_eq_abs] using massPartitionRemainder_linear
          (fun i => M (massTimeMesh T n i) ω) (n+1)
      _ ≤ 4*((A T ω-A 0 ω)+(B T ω-B 0 ω)) :=
        mul_le_mul_of_nonneg_left (massDifference_mesh_variation
          (fun t => A t ω) (fun t => B t ω) ha hb T n) (by norm_num)
      _ = _ := by simp only [ha0,hb0,Pi.zero_apply,sub_zero]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
    filter_upwards [hA,hB,hcont] with ω ha hb hc
    exact massDifference_mesh_remainder_tendsto (fun t => A t ω) (fun t => B t ω) ha hb T hc
  have hI := tendsto_integral_of_dominated_convergence (fun ω => 4*(A T ω+B T ω))
    (fun n => (hXint n).aestronglyMeasurable) ((hAI.add hBI).const_mul 4) hbound hlim
  simp only [integral_zero,hXmean] at hI
  have htest0 : (∫ ω, massSeparationTest (M T ω) ∂P) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hI
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun ω => massSeparationTest_nonneg (M T ω))
    (martingale_mass_test_integrable hM T)).mp htest0
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp ((massSeparationTest_eq_zero (M T ω)).mp hω)

/-- The fixed-time result holds simultaneously at every time by continuity and
a countable dense family of deterministic times. -/
theorem increasing_mass_martingale_indistinguishable
    (hM : Martingale (fun t ω => A t ω-B t ω) ℱ P)
    (hA : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hB : ∀ᵐ ω ∂P, Monotone (fun t => B t ω))
    (hA0 : A 0 =ᵐ[P] 0) (hB0 : B 0 =ᵐ[P] 0)
    (hAI : ∀ T, Integrable (A T) P) (hBI : ∀ T, Integrable (B T) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => A t ω-B t ω)) :
    ∀ᵐ ω ∂P, ∀ t, A t ω = B t ω := by
  have heq (t : ℝ≥0) : A t =ᵐ[P] B t :=
    increasing_mass_martingale_eq_at A B hM hA hB hA0 hB0 t (hAI t) (hBI t)
      (hcont.mono (fun _ h => h.continuousOn))
  have hcount : ∀ᵐ ω ∂P, ∀ n : ℕ,
      A (TopologicalSpace.denseSeq ℝ≥0 n) ω = B (TopologicalSpace.denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => heq _)
  filter_upwards [hcount,hcont] with ω he hc
  have hfun : (fun t => A t ω-B t ω) = fun _ => 0 :=
    (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer hc continuous_const
      (funext (fun n => sub_eq_zero.mpr (he n)))
  intro t
  exact sub_eq_zero.mp (congr_fun hfun t)

end SLEExactGauge

end

end OAI
