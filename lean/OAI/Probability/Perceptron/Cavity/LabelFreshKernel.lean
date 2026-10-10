import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshDiagonalNoise
import OAI.Probability.Perceptron.Cavity.FreshMomentLimit
import OAI.Probability.Perceptron.Variational.SynchronizedLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceLabelLevel_val_injective (k : ℕ) :
    Function.Injective (fun l : Fin (k+1) => (sourceLabelLevel k l).val) := by
  intro i j hij
  apply Fin.ext
  have h : (i.val:ℝ)=(j.val:ℝ) := by
    apply (div_left_inj' (show (k+1:ℕ)≠(0:ℝ) by positivity)).mp
    exact hij
  exact_mod_cast h

def labelProfileInterpolant {k : ℕ} (q : Fin (k+1)→ℝ) : Time →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun u => (Lagrange.interpolate Finset.univ (fun l => (sourceLabelLevel k l).val) q).eval u.val,
      by fun_prop⟩

lemma labelProfileInterpolant_node {k : ℕ} (q : Fin (k+1)→ℝ) (l : Fin (k+1)) :
    labelProfileInterpolant q (sourceLabelLevel k l)=q l := by
  exact Lagrange.eval_interpolate_at_node q (sourceLabelLevel_val_injective k).injOn (Finset.mem_univ l)

def labelFreshBlockKernel {k : ℕ} (q : Fin (k+1)→ℝ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    CompactBlock CompactJointOverlap r →ᵇ ℝ :=
  (freshReplicaMatrixKernel f r).compContinuous
    ⟨fun Q => fun i j => if i=j then 1 else labelProfileInterpolant q (Q i j).2,
      by
        classical
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        by_cases hij : i=j
        · simp only [ite_eq_left hij]
          exact continuous_const
        · simp only [ite_eq_right hij]
          fun_prop⟩

def labelFreshArrayKernel {k : ℕ} (q : Fin (k+1)→ℝ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    CompactArray CompactJointOverlap →ᵇ ℝ :=
  (labelFreshBlockKernel q f r).compContinuous ⟨compactBlock r,compactBlock_continuous r⟩

lemma labelFreshBlockKernel_source {N k : ℕ} (q : Fin (k+1)→ℝ) (f : ℝ →ᵇ ℝ) (r : ℕ)
    (xs : Fin r→NormalizedSpin N×IndexedLeaf k) :
    labelFreshBlockKernel q f r (fun i j => sourceJointOverlap (xs i) (xs j))=
      freshReplicaMatrixKernel f r
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2)) := by
  apply congrArg (freshReplicaMatrixKernel f r)
  funext i j
  change (if i=j then 1 else labelProfileInterpolant q (sourceJointOverlap (xs i) (xs j)).2)=_
  split_ifs with h
  · rfl
  · exact labelProfileInterpolant_node q _

lemma labelProfile_gibbs_moment {S : Type} [MeasurableSpace S] {k : ℕ}
    (q : Fin (k+1)→ℝ) (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (μ : Measure (S×IndexedLeaf k)) [IsProbabilityMeasure μ]
    (H : S×IndexedLeaf k→ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) μ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (tiltMean μ H (fun x => gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ f
      (labelProfileField q g x)) 1)^r ∂countableGaussianLaw)=
      gibbsReplicaMean μ H r (fun xs => freshReplicaMatrixKernel f r
        (fun i j => if i=j then 1 else q (indexedCommonDepth k (xs j).2 (xs i).2))) := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  simp_rw [← tilt_law_integral_of_integrable μ hH he1]
  rw [gibbsReplicaMean_integral_of_integrable μ hH he]
  exact labelProfile_diagonal_one_moment q h0 hq h1 (tiltLaw μ H 1) f r

def sourceLabelFreshMoment (n k : ℕ) (q : Fin (k+1)→ℝ) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) : ℝ :=
  ∫ a, ∫ g, (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => gaussianAverageBCF ⟨1-q (Fin.last k),sub_nonneg.mpr h1⟩ ψ
      (labelProfileField q g x)) 1)^r ∂countableGaussianLaw
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

lemma sourceLabelFreshMoment_array (n k : ℕ) (q : Fin (k+1)→ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1)
    (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ)
    (hh0 : ∀ i, 0≤h i) (hh : Monotone h) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) :
    sourceLabelFreshMoment n k q h1 f ψ p d h u z t r=
      ∫ Q, labelFreshArrayKernel q ψ r Q ∂sourceGibbsArrayLaw n k f p d h u z t := by
  have hblock := sourceGibbsArray_block_integral n k f p d h hh0 hh u z t r
    (labelFreshBlockKernel q ψ r).measurable (fun Q => (labelFreshBlockKernel q ψ r).norm_coe_le_norm Q)
  change (∫ Q, labelFreshArrayKernel q ψ r Q ∂sourceGibbsArrayLaw n k f p d h u z t)=_ at hblock
  rw [hblock]
  unfold sourceLabelFreshMoment
  apply integral_congr_ae
  filter_upwards [sourceFresh_exp_ae n k f p d h hh0 hh u z t] with a ha
  rw [labelProfile_gibbs_moment q h0 hq h1 _ _
    (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left ha]
  congr 1
  funext xs
  exact (labelFreshBlockKernel_source q ψ r xs).symm

theorem sourceLabelFreshMoment_tendsto (k : ℕ) (q : Fin (k+1)→ℝ)
    (h0 : 0≤q 0) (hq : Monotone q) (h1 : q (Fin.last k)≤1) (f ψ : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (r : ℕ) :
    Tendsto (fun n => sourceLabelFreshMoment (s n) k q h1 f ψ (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n)) r) atTop
      (𝓝 (∫ Q, labelFreshArrayKernel q ψ r Q ∂ν)) := by
  simp_rw [sourceLabelFreshMoment_array _ _ _ h0 hq h1 _ _ _ _ _ (hh0 _) (hh _)]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (labelFreshArrayKernel q ψ r)).continuousAt.tendsto.comp hlim

end SphericalPerceptronFreeEnergy
end

end OAI
