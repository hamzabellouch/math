import Mathlib
import OAI.Probability.Perceptron.Variational.TiltMeanCenteredAbsSq
import OAI.Probability.Perceptron.Variational.GaussianCoupling
import OAI.Probability.Perceptron.Variational.IndexedGaussianCovariance

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma sourceEnrichedFeature_add_single (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ)
    (j : Fin N) (a : ℝ) (x : NormalizedSpin N) (i : EnrichedIndex N N p) :
    sourceEnrichedFeature N p (u+Pi.single j a) x i =
      sourceEnrichedFeature N p u x i+
        a*perturbationAmplitude N (fun _ => 1) j*sourceGaussianTestFeature N p j x i := by
  classical
  cases i with
  | inl i => simp [sourceEnrichedFeature,sourceGaussianTestFeature,enrichedFeature]
  | inr i =>
    rcases i with ⟨l,r⟩
    by_cases hl : l=j
    · subst l
      simp only [sourceEnrichedFeature,sourceGaussianTestFeature,enrichedFeature,perturbationAmplitude,
        Pi.add_apply,Pi.single_eq_same,mul_one]
      ring
    · simp [sourceEnrichedFeature,sourceGaussianTestFeature,enrichedFeature,perturbationAmplitude,
        Pi.single_apply,hl]

lemma sourceGaussianRow_add_single {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (j : Fin N) (a : ℝ) (i : ℕ) (x : NormalizedSpin N×IndexedLeaf k) :
    sourceGaussianRow p d h (u+Pi.single j a) i x =
      sourceGaussianRow p d h u i x+
        a*perturbationAmplitude N (fun _ => 1) j*sourceGaussianTestRow p d h j i x := by
  unfold sourceGaussianRow sourceGaussianTestRow indexedGaussianRow finiteGaussianRow
  simp_rw [sourceEnrichedFeature_add_single]
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

lemma enrichedIndexedHamiltonian_add_single (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (v : ℝ) (g : ℕ → ℝ)
    (x : NormalizedSpin (n+1)×IndexedLeaf k) :
    enrichedIndexedHamiltonian n M k f a p d h (u+Pi.single j v) g x =
      enrichedIndexedHamiltonian n M k f a p d h u g x+
        v*perturbationAmplitude (n+1) (fun _ => 1) j*
          countableGaussianField (sourceGaussianTestRow p d h j)
            (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) g x := by
  unfold enrichedIndexedHamiltonian countableGaussianHamiltonian
  have hr : sourceGaussianRow p d h (u+Pi.single j v) = fun i x =>
      sourceGaussianRow p d h u i x+
        (v*perturbationAmplitude (n+1) (fun _ => 1) j)*sourceGaussianTestRow p d h j i x := by
    funext i x
    exact sourceGaussianRow_add_single p d h u j v i x
  rw [hr,countableGaussianField_add,countableGaussianField_smul]
  ring

lemma coupling_log_contDiff {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) :
    ContDiff ℝ 2 (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
  let ρ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (H x)))
  have hf : cgf Y ρ = (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
    funext b
    exact congrArg Real.log (coupling_mgf_identity μ hH b)
  rw [← hf,contDiff_iff_contDiffAt]
  intro a
  apply AnalyticAt.contDiffAt
  apply analyticAt_cgf
  rw [coupling_expSet μ hH hY he,interior_univ]
  trivial

lemma coupling_log_convex {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) :
    ConvexOn ℝ univ (fun b => Real.log (tiltPartition μ (fun x => H x+b*Y x) 1)) := by
  have hs := coupling_log_contDiff μ hH hY he
  apply convexOn_of_deriv2_nonneg' convex_univ
    (hs.differentiable (by norm_num)).differentiableOn
    ( (ContDiff.deriv' (n := 1) hs).differentiable (by norm_num)).differentiableOn
  intro a _
  rw [← iteratedDeriv_eq_iterate,coupling_log_second_derivative μ hH hY he]
  exact tiltMean_nonneg μ (fun _ => sq_nonneg _) 1

lemma convex_derivative_local_bound {F D : ℝ → ℝ}
    (hc : ConvexOn ℝ univ F) (hd : ∀ x, HasDerivAt F (D x) x) (u v : ℝ)
    (hv : v ∈ Ioo (u-1) (u+1)) :
    |D v| ≤ |F (u-2)|+|F (u-1)|+|F (u+1)|+|F (u+2)| := by
  have hmono : Monotone D := by
    intro x y hxy
    simpa only [(hd x).deriv,(hd y).deriv] using
      hc.monotoneOn_deriv (fun x _ => (hd x).differentiableAt) (mem_univ x) (mem_univ y) hxy
  have hl := hc.slope_le_of_hasDerivAt (mem_univ (u-2)) (mem_univ (u-1))
    (by linarith : u-2 < u-1) (hd (u-1))
  have hr := hc.le_slope_of_hasDerivAt (mem_univ (u+1)) (mem_univ (u+2))
    (by linarith : u+1 < u+2) (hd (u+1))
  have hl' : F (u-1)-F (u-2) ≤ D v := by
    have hh : (u-1)-(u-2) = (1:ℝ) := by ring
    simp only [slope,hh,inv_one,one_smul] at hl
    exact hl.trans (hmono hv.1.le)
  have hr' : D v ≤ F (u+2)-F (u+1) := by
    have hh : (u+2)-(u+1) = (1:ℝ) := by ring
    simp only [slope,hh,inv_one,one_smul] at hr
    exact (hmono hv.2.le).trans hr
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (F (u-1)),le_abs_self (F (u-2)),abs_nonneg (F (u+1)),abs_nonneg (F (u+2))]
  · linarith [le_abs_self (F (u+2)),neg_abs_le (F (u+1)),abs_nonneg (F (u-1)),abs_nonneg (F (u-2))]

lemma annealed_convex_hasDerivAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F D : ℝ → Ω → ℝ} (hF : ∀ t, AEStronglyMeasurable (F t) P)
    (hD : ∀ t, AEStronglyMeasurable (D t) P) (hi : ∀ t, Integrable (F t) P)
    (hc : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun t => F t ω) ∧ ∀ t, HasDerivAt (fun t => F t ω) (D t ω) t)
    (u : ℝ) :
    Integrable (D u) P ∧ HasDerivAt (fun t => ∫ ω, F t ω ∂P) (∫ ω, D u ω ∂P) u := by
  let B : Ω → ℝ := fun ω => |F (u-2) ω|+|F (u-1) ω|+|F (u+1) ω|+|F (u+2) ω|
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : u-1 < u) (by linarith : u < u+1))
    (Eventually.of_forall hF) (hi u) (hD u)
  · filter_upwards [hc] with ω hω t ht
    rw [Real.norm_eq_abs]
    exact convex_derivative_local_bound hω.1 hω.2 u t ht
  · exact (((hi (u-2)).abs.add (hi (u-1)).abs).add (hi (u+1)).abs).add (hi (u+2)).abs
  · filter_upwards [hc] with ω hω t _
    exact hω.2 t

end SphericalPerceptronFreeEnergy

end

end OAI
