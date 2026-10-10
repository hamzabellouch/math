import Mathlib
import OAI.Probability.Perceptron.Variational.EnrichedUniformBounds
import OAI.Probability.Perceptron.Pressure.IndexedGibbsPartition
import OAI.Probability.Perceptron.Variational.GaussianBoltzmann
import OAI.Probability.Perceptron.Brownian.GaussianFieldAlgebra

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

section
variable {S : Type*} [MeasurableSpace S]
variable (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_integrable_of_integer_endpoints {H Y : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ k : ℕ, Integrable (fun x => Real.exp (H x+(k:ℝ)*Y x)) μ ∧
      Integrable (fun x => Real.exp (H x-(k:ℝ)*Y x)) μ) (a : ℝ) :
    Integrable (fun x => Real.exp (H x+a*Y x)) μ := by
  obtain ⟨k,hk⟩ := exists_nat_gt |a|
  refine ((he k).1.add (he k).2).mono' ((hH.add (hY.const_mul a)).exp.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hy : 0 ≤ Y x
  · have ha : a ≤ (k:ℝ) := (le_abs_self a).trans hk.le
    exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_right ha hy) _)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have ha : -(k:ℝ) ≤ a := by linarith [neg_abs_le a]
    have hh : H x+a*Y x ≤ H x-(k:ℝ)*Y x := by
      have h := mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)
      nlinarith
    exact (Real.exp_le_exp.mpr hh).trans (le_add_of_nonneg_left (Real.exp_pos _).le)

variable {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
variable (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)
include hW hv hw hL hA hD hE

lemma countableGaussian_coupling_exp_ae (a : ℝ) :
    ∀ᵐ g ∂countableGaussianLaw, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)) μ := by
  have hm (i : ℕ) : Measurable (fun x => v i x+a*w i x) := (hv i).add ((hw i).const_mul a)
  have hb (x : S) : (∑ i : Fin (L x), (v i.val x+a*w i.val x)^2) ≤ 2*D+2*a^2*E := by
    simpa only [gaussianTailCoefficient,zero_le,ite_true,one_mul,mul_one,one_pow] using
      gaussianCombinedCoefficient_sq_bound v w L hD hE 1 a 0 x
  have he := (countableGaussianHamiltonian_exp_joint_integrable μ hW hm hL hA hb 1).prod_left_ae
  filter_upwards [he] with g hg
  convert hg using 1
  ext x
  simp only [one_mul,countableGaussianHamiltonian,countableGaussianField_add,
    countableGaussianField_smul]
  congr 1
  ring

lemma countableGaussian_all_coupling_exp_ae :
    ∀ᵐ g ∂countableGaussianLaw, ∀ a : ℝ, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)) μ := by
  have hp : ∀ᵐ g ∂countableGaussianLaw, ∀ k : ℕ, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x+(k:ℝ)*countableGaussianField w L g x)) μ :=
    ae_all_iff.mpr fun k => countableGaussian_coupling_exp_ae μ hW hv hw hL hA hD hE k
  have hn : ∀ᵐ g ∂countableGaussianLaw, ∀ k : ℕ, Integrable (fun x => Real.exp
      (countableGaussianHamiltonian W v L g x-(k:ℝ)*countableGaussianField w L g x)) μ := by
    apply ae_all_iff.mpr
    intro k
    simpa only [neg_mul,sub_eq_add_neg] using
      countableGaussian_coupling_exp_ae μ hW hv hw hL hA hD hE (-(k:ℝ))
  filter_upwards [hp,hn] with g hgp hgn a
  exact coupling_integrable_of_integer_endpoints μ
    ((countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id))
    ((countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id))
    (fun k => ⟨hgp k,hgn k⟩) a

lemma countableGaussian_coupling_derivatives_ae :
    ∀ᵐ g ∂countableGaussianLaw, ∀ a : ℝ,
      HasDerivAt (fun b => Real.log (tiltPartition μ (fun x =>
        countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1))
        (tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
          (countableGaussianField w L g) 1) a ∧
      iteratedDeriv 2 (fun b => Real.log (tiltPartition μ (fun x =>
        countableGaussianHamiltonian W v L g x+b*countableGaussianField w L g x) 1)) a =
        tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
          (fun x => (countableGaussianField w L g x-
            tiltMean μ (fun x => countableGaussianHamiltonian W v L g x+a*countableGaussianField w L g x)
              (countableGaussianField w L g) 1)^2) 1 := by
  filter_upwards [countableGaussian_all_coupling_exp_ae μ hW hv hw hL hA hD hE] with g hg a
  have hH : Measurable (countableGaussianHamiltonian W v L g) := (countableGaussianHamiltonian_measurable hW hv hL).comp (measurable_const.prodMk measurable_id)
  have hY : Measurable (countableGaussianField w L g) := (countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id)
  exact ⟨coupling_log_hasDerivAt μ hH hY hg a,coupling_log_second_derivative μ hH hY hg a⟩
end

def enrichedIndexedBaseMeasure (n k : ℕ) (b : IndexedCascadeBase k) :
    Measure (NormalizedSpin (n+1) × IndexedLeaf k) :=
  (unitSphereLaw (n+1)).prod (indexedLeafProbability k b)

instance enrichedIndexedBaseMeasure_probability (n k : ℕ) (b : IndexedCascadeBase k) :
    IsProbabilityMeasure (enrichedIndexedBaseMeasure n k b) := by
  unfold enrichedIndexedBaseMeasure
  infer_instance

def enrichedIndexedBoundedEnergy (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (x : NormalizedSpin (n+1) × IndexedLeaf k) : ℝ :=
  normalizedPatternEnergy (n+1) M f a x.1-(n+1:ℕ)*h (Fin.last k)

lemma enrichedIndexedBoundedEnergy_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) :
    Measurable (enrichedIndexedBoundedEnergy n M k f a h) :=
  ((normalizedPatternEnergy_continuous (n+1) M f).measurable.comp
    (measurable_const.prodMk measurable_fst)).sub measurable_const

lemma enrichedIndexedBoundedEnergy_bound (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ)
    (x : NormalizedSpin (n+1) × IndexedLeaf k) :
    |enrichedIndexedBoundedEnergy n M k f a h x| ≤ (M:ℝ)*‖f‖+|(n+1:ℕ)*h (Fin.last k)| :=
  (abs_sub _ _).trans (add_le_add (normalizedPatternEnergy_bound (n+1) M f a x.1) le_rfl)

def enrichedIndexedHamiltonian (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (g : ℕ → ℝ) :
    NormalizedSpin (n+1) × IndexedLeaf k → ℝ :=
  countableGaussianHamiltonian (enrichedIndexedBoundedEnergy n M k f a h)
    (sourceGaussianRow p d h u) (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k) g

lemma sourceEnrichedFeature_measurable (N : ℕ) (p : Fin N → ℕ) (u : Fin N → ℝ) :
    Measurable (sourceEnrichedFeature N p u) :=
  (enrichedFeature_continuous N N p (Real.sqrt N) (perturbationAmplitude N u)).measurable

lemma enrichedIndexedHamiltonian_spin_partition (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (g : ℕ → ℝ)
    (b : IndexedCascadeBase k) :
    tiltPartition (enrichedIndexedBaseMeasure n k b)
      (enrichedIndexedHamiltonian n M k f a p d h u g) 1 =
    ∫ l, Real.exp (enrichedTerminal n M f a p u (h (Fin.last k))
      (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
        ((fun _ => enrichedRootMap p d h (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1),
          (indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2) l 0))
      ∂indexedLeafProbability k b := by
  let root := profileGaussianRoot (enrichedCoordinateLevel p d h)
  let step := profileGaussianStep (enrichedCoordinateLevel p d h)
  have hWc : Continuous (normalizedPatternEnergy (n+1) M f a) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)
  have hWm := hWc.measurable
  have hp := indexedGaussian_spin_partition (unitSphereLaw (n+1)) hWm
    (sourceEnrichedFeature_measurable (n+1) p u)
    (normalizedPatternEnergy_bound (n+1) M f a)
    (fun x => (sourceEnrichedFeature_norm (n+1) p u x).le) k root step b ((n+1:ℕ)*h (Fin.last k)) g
  have hA : enrichedIncrementMap p d h = fun j => diagonalMark (step j) :=
    funext (enrichedIncrementMap_profile p d h)
  have hR : enrichedRootMap p d h = diagonalMark root := rfl
  rw [hA,hR]
  unfold enrichedIndexedBaseMeasure
  convert hp using 2
  · funext x
    unfold enrichedIndexedHamiltonian countableGaussianHamiltonian enrichedIndexedBoundedEnergy sourceGaussianRow
    dsimp only [root,step]
    ring
  · rfl

lemma enrichedIndexedHamiltonian_partition (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (a : Fin M → Fin (n+1) → ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (u : Fin (n+1) → ℝ) (g : ℕ → ℝ)
    (b : IndexedCascadeBase k) (hb : IndexedCascadeGood k b)
    (hb' : 0 < ((indexedLeafMeasure k b) univ).toReal) :
    Real.log (tiltPartition (enrichedIndexedBaseMeasure n k b)
      (enrichedIndexedHamiltonian n M k f a p d h u g) 1) =
      enrichedCascadeLog n M k f a p d u h
        ((indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).1,
          indexedCascadeRealize k (b,(indexedGaussianDisorder k (EnrichedIndex (n+1) (n+1) p) g).2)) := by
  rw [enrichedIndexedHamiltonian_spin_partition]
  have hH : Measurable (fun x : ℕ → EnrichedMark (n+1) (n+1) p =>
      enrichedTerminal n M f a p u (h (Fin.last k)) (x 0)) :=
    (enrichedTerminal_lipschitz n M f a p u _).continuous.measurable.comp (measurable_pi_apply 0)
  rw [indexedLeafProbability_terminal_integral
    (gaussianMarkLaw : ProbabilityMeasure (EnrichedMark (n+1) (n+1) p))
    (gaussianLinearMarkStep_measurable (enrichedIncrementMap p d h)) hH k b hb hb']
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
