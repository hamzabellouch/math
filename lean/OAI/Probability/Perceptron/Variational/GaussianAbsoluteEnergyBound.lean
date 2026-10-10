import Mathlib
import OAI.Probability.Perceptron.Variational.Contact

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma gaussianEnergy_abs_tilt_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    {W : S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
    (hW : Measurable W) (hv : ∀ i, Measurable (v i)) (hw : ∀ i, Measurable (w i))
    (hL : Measurable L) {A D E : ℝ} (hA : ∀ x, |W x| ≤ A)
    (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
    (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E) :
    (∫ g, tiltMean μ (countableGaussianHamiltonian W v L g)
      (fun x => |countableGaussianField w L g x|) 1 ∂countableGaussianLaw) ≤
      Real.exp (2*A+2*D)+4*Real.exp (2*A+4*D+E) := by
  have hZ := gaussianHamiltonianPartition_inverse_power_integrable μ hW hv hL hA hD 2
  have hY := gaussianEnergy_weighted_moment_joint_integrable hW hv hw hL hA hD hE μ 0 2 2
  simp only [gaussianTailCoefficient_zero,sq_abs] at hY
  have hb := tiltMean_abs_annealed_L2_bound μ countableGaussianLaw
    (countableGaussianHamiltonian_measurable hW hv hL)
    (countableGaussianField_measurable hw hL) hZ hY
  have hz := gaussianHamiltonianPartition_inverse_power_bound μ hW hv hL hA hD 2
  norm_num only [Nat.cast_ofNat] at hz
  have hze : (2:ℝ)*A+4*D/2=2*A+2*D := by ring
  rw [hze] at hz
  have hy : (∫ q : S×(ℕ → ℝ), countableGaussianField w L q.2 q.1^2*
      Real.exp (2*countableGaussianHamiltonian W v L q.2 q.1) ∂(μ.prod countableGaussianLaw)) ≤
      4*Real.exp (2*A+4*D+E) := by
    rw [integral_prod _ hY]
    have hi := hY.integral_prod_left
    have hm := integral_mono hi (integrable_const (4*Real.exp (2*A+4*D+E))) (fun x => by
      simpa only [gaussianTailCoefficient_zero,sq_abs,Nat.factorial_two,Nat.cast_ofNat,
        abs_of_pos (by norm_num : (0:ℝ)<2),show (2:ℝ)^2=4 by norm_num,
        show (2:ℝ)*2=4 by norm_num] using
        gaussianEnergy_weighted_moment_bound hW hv hw hL hA hD hE 0 2 2 x)
    simpa using hm
  let a := ∫ g, (tiltPartition μ (countableGaussianHamiltonian W v L g) 1)⁻¹^2 ∂countableGaussianLaw
  let b := ∫ q : S×(ℕ → ℝ), countableGaussianField w L q.2 q.1^2*
      Real.exp (2*countableGaussianHamiltonian W v L q.2 q.1) ∂(μ.prod countableGaussianLaw)
  have ha0 : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hs : Real.sqrt a*Real.sqrt b ≤ a+b := by
    have hsa := Real.sq_sqrt ha0
    have hsb := Real.sq_sqrt hb0
    nlinarith [sq_nonneg (Real.sqrt a-Real.sqrt b)]
  exact hb.trans (hs.trans (add_le_add hz hy))

lemma poisson_exp_affine_integrable (r : ℝ≥0) (a b : ℝ) :
    Integrable (fun M : ℕ => Real.exp (a*(M:ℝ)+b)) (poissonMeasure r) := by
  have hi : Integrable (fun M : ℕ => (Real.exp a)^M) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    have he := (NormedSpace.expSeries_div_hasSum_exp ((r:ℝ)*Real.exp a)).summable.mul_left (Real.exp (-(r:ℝ)))
    apply he.congr
    intro M
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Real.exp_pos a).le M),mul_pow]
    ring
  convert hi.mul_const (Real.exp b) using 1
  ext M
  rw [Real.exp_add,mul_comm a (M:ℝ),Real.exp_nat_mul]

lemma sourceCoupling_abs_energy_integrable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (h : Fin (k+1) → ℝ)
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (u : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (z : Fin k → ℝ) (t : ℝ≥0) :
    Integrable (fun a => tiltMean (sourceSpinLeafKernel n k a.1)
      (sourceCouplingHamiltonian n k f p d h u a)
      (fun x => |sourceCouplingEnergy n k p d h j a x|) 1)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
  let L : (NormalizedSpin (n+1) × IndexedLeaf k) → ℕ := indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k
  let Y := countableGaussianField (sourceGaussianTestRow p d h j) L
  let F := fun a : SourceBaseData n k × (ℕ → ℝ) =>
    tiltMean (sourceSpinLeafKernel n k a.1) (sourceCouplingHamiltonian n k f p d h u a)
      (fun x => |Y a.2 x|) 1
  let D := (2*h (Fin.last k)+1)*(enrichedFeatureBound (n+1) u:ℝ)^2
  let E := 2*h (Fin.last k)+1
  let A := fun M : ℕ => (M:ℝ)*‖f‖+|(n+1:ℕ)*h (Fin.last k)|
  let B := fun M : ℕ => Real.exp (2*A M+2*D)+4*Real.exp (2*A M+4*D+E)
  have hY : Measurable (fun a : (SourceBaseData n k × (ℕ → ℝ)) ×
      (NormalizedSpin (n+1) × IndexedLeaf k) => Y a.1.2 a.2) :=
    measurable_disorder_state_lift (countableGaussianField_measurable
      (sourceGaussianTestRow_measurable p d h j) (indexedGaussianRowLength_measurable k))
  have hm : Measurable F := kernel_tiltMean_measurable (sourceFullSpinLeafKernel n k)
    (sourceCouplingHamiltonian_measurable n k f p d h u) hY.abs
  have hf (a : SourceBaseData n k) : Integrable (fun g => F (a,g)) countableGaussianLaw := by
    rw [show (fun g => F (a,g)) = fun g => tiltMean (enrichedIndexedBaseMeasure n k a.2.2)
      (enrichedIndexedHamiltonian n a.1 k f (patternPrefix (n+1) a.1 a.2.1) p d h u g)
      (fun x => |Y g x|) 1 by funext g; simp only [F,sourceSpinLeafKernel_apply,sourceCouplingHamiltonian]]
    simpa only [gaussianTailCoefficient_zero,enrichedIndexedHamiltonian] using
      gaussianEnergy_tail_tilt_integrable (enrichedIndexedBaseMeasure n k a.2.2)
        (enrichedIndexedBoundedEnergy_measurable n a.1 k f _ h)
        (sourceGaussianRow_measurable p d h u) (sourceGaussianTestRow_measurable p d h j)
        (indexedGaussianRowLength_measurable k)
        (enrichedIndexedBoundedEnergy_bound n a.1 k f _ h)
        (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
        (sourceGaussianTestRow_square_bound p d h hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)) j) 0
  have hb (a : SourceBaseData n k) : (∫ g, F (a,g) ∂countableGaussianLaw) ≤ B a.1 := by
    simpa only [F,sourceCouplingHamiltonian,sourceSpinLeafKernel_apply,enrichedIndexedHamiltonian,
      B,A,D,E] using gaussianEnergy_abs_tilt_bound (enrichedIndexedBaseMeasure n k a.2.2)
        (enrichedIndexedBoundedEnergy_measurable n a.1 k f _ h)
        (sourceGaussianRow_measurable p d h u) (sourceGaussianTestRow_measurable p d h j)
        (indexedGaussianRowLength_measurable k)
        (enrichedIndexedBoundedEnergy_bound n a.1 k f _ h)
        (sourceGaussianRow_square_bound p d h u hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)))
        (sourceGaussianTestRow_square_bound p d h hh0 hh (hh0 (Fin.last k)) (fun l => hh (Fin.le_last l)) j)
  have hbi : Integrable B (poissonMeasure ((n+1:ℕ)*t)) := by
    have h1 := poisson_exp_affine_integrable ((n+1:ℕ)*t) (2*‖f‖) (2*|(n+1:ℕ)*h (Fin.last k)|+2*D)
    have h2 := poisson_exp_affine_integrable ((n+1:ℕ)*t) (2*‖f‖) (2*|(n+1:ℕ)*h (Fin.last k)|+4*D+E)
    apply (h1.add (h2.const_mul 4)).congr
    filter_upwards [] with M
    dsimp [B,A]
    congr 2 <;> ring_nf
  have hbi' : Integrable (fun a : SourceBaseData n k => B a.1) (sourceBaseDataLaw n k z t) :=
    measurePreserving_fst.integrable_comp_of_integrable hbi
  have hF0 (a) : 0 ≤ F a := tiltMean_nonneg _ (fun _ => abs_nonneg _) 1
  have hFi : Integrable F ((sourceBaseDataLaw n k z t).prod countableGaussianLaw) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨ae_of_all _ hf, ?_⟩
    apply hbi'.mono' (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    filter_upwards [] with a
    simp only [Real.norm_eq_abs,abs_of_nonneg (hF0 _)]
    rw [abs_of_nonneg (integral_nonneg fun g => hF0 (a,g))]
    exact hb a
  convert hFi.const_mul |perturbationAmplitude (n+1) (fun _ => 1) j| using 1
  ext a
  simp only [sourceCouplingEnergy,abs_mul,F,Y,tiltMean,tiltIntegral,one_mul]
  rw [show (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x)*
      (|perturbationAmplitude (n+1) (fun _ => 1) j| *|Y a.2 x|)) =
      fun x => |perturbationAmplitude (n+1) (fun _ => 1) j| *
        (Real.exp (sourceCouplingHamiltonian n k f p d h u a x)*|Y a.2 x|) by funext x; ring,
      integral_const_mul]
  ring

end SphericalPerceptronFreeEnergy

end

end OAI
