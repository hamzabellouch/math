import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.GaussianImages

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
open Metric Matrix WithLp

noncomputable def gaussianRows (k d : ℕ) : Measure (Fin k → Fin d → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))

noncomputable def projectVector {k d : ℕ} (X : Fin k → Fin d → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : Fin k → ℝ := fun r => ∑ j, X r j * v j

lemma continuous_projectVector {k d : ℕ} :
    Continuous (fun p : (Fin k → Fin d → ℝ) × EuclideanSpace ℝ (Fin d) => projectVector p.1 p.2) := by
  unfold projectVector
  fun_prop

lemma projectVector_sub {k d : ℕ} (X : Fin k → Fin d → ℝ)
    (v w : EuclideanSpace ℝ (Fin d)) : projectVector X (v-w) = projectVector X v-projectVector X w := by
  ext r
  simp only [projectVector, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply]

lemma projectVector_rowMatrix {k q d : ℕ} (X : Fin k → Fin d → ℝ)
    (v : Fin q → EuclideanSpace ℝ (Fin d)) (r : Fin k) (i : Fin q) :
    projectVector X (v i) r = (rowMatrix v *ᵥ X r) i := by
  simp only [projectVector, mulVec, dotProduct, rowMatrix]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma boxScale_cancel (k q : ℕ) (η : ℝ) (hη : 0 < η) :
    boxScale k η ^ q * ENNReal.ofReal ((4*η)^(q*k)) = ENNReal.ofReal ((2:ℝ)^(k*q)) := by
  have h2 : 0 < 2*η := by positivity
  have he : (4*η)^(q*k) = (2:ℝ)^(k*q)*((2*η)^k)^q := by
    rw [show (4:ℝ)*η=2*(2*η) by ring, mul_pow, ← pow_mul, Nat.mul_comm q k]
  rw [he, ENNReal.ofReal_mul (pow_nonneg (by positivity) _),
    ENNReal.ofReal_pow (pow_nonneg h2.le _), boxScale, ← ENNReal.inv_pow,
    mul_left_comm, ENNReal.inv_mul_cancel (by positivity) (by finiteness), mul_one]

lemma fixedReplica_moment_le {k q d : ℕ} (hk : 0 < k)
    (η : ℝ) (hη : 0 < η) (v : Fin (q+1) → EuclideanSpace ℝ (Fin d)) :
    (∫⁻ p : (Fin k → Fin d → ℝ) × (Fin k → ℝ),
      ∏ i, boxKernel η (projectVector p.1 (v i)) p.2 ∂(gaussianRows k d).prod volume) ≤
      ENNReal.ofReal ((2:ℝ)^(k*q)) * gramInverseProduct k (fun i : Fin q => v i.succ-v 0) := by
  classical
  let diff := fun i : Fin q => v i.succ-v 0
  let D := {X : Fin k → Fin d → ℝ | ∀ (i : Fin q) r,
      |projectVector X (v i.succ) r-projectVector X (v 0) r| ≤ 2*η}
  have hD : MeasurableSet D := by
    dsimp only [D]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro r
    exact measurableSet_le
      ((((measurable_pi_apply r).comp (continuous_projectVector.measurable.comp
        (measurable_id.prodMk measurable_const))).sub
        ((measurable_pi_apply r).comp (continuous_projectVector.measurable.comp
          (measurable_id.prodMk measurable_const)))).abs) measurable_const
  have hdiff : D = {X : Fin k → Fin d → ℝ | ∀ r i, |(rowMatrix diff *ᵥ X r) i| ≤ 2*η} := by
    ext X
    simp only [D, Set.mem_ofPred_eq]
    rw [forall_comm]
    congr! 2
    simp only [← projectVector_rowMatrix, diff, projectVector_sub, Pi.sub_apply]
  have hprob : gaussianRows k d D ≤ gramInverseProduct k diff *
      ENNReal.ofReal ((4*η)^(q*k)) := by
    rw [hdiff, gramInverseProduct_eq_inverseVolume]
    simpa only [gaussianRows, Fintype.card_fin, rowMatrix_gram, show 2*(2*η)=4*η by ring] using
      gaussian_multirow_box_le_extended (ρ := Fin k) (by simpa using hk)
        (rowMatrix diff) (2*η) (by positivity)
  have hmeas : Measurable (fun p : (Fin k → Fin d → ℝ) × (Fin k → ℝ) =>
      ∏ i, boxKernel η (projectVector p.1 (v i)) p.2) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_boxKernel η).comp
      ((continuous_projectVector.measurable.comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd)
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc
    _ ≤ ∫⁻ X, D.indicator (fun _ => boxScale k η ^ q) X ∂gaussianRows k d := by
      apply lintegral_mono
      intro X
      simpa only [Set.indicator, D, Set.mem_ofPred_eq] using
        lintegral_boxKernel_product_le η hη (fun i => projectVector X (v i))
    _ = boxScale k η ^ q * gaussianRows k d D := by
      rw [lintegral_indicator hD, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ boxScale k η ^ q * (gramInverseProduct k diff * ENNReal.ofReal ((4*η)^(q*k))) :=
      mul_le_mul_right hprob _
    _ = ENNReal.ofReal ((2:ℝ)^(k*q)) * gramInverseProduct k diff := by
      rw [mul_left_comm, boxScale_cancel k q η hη, mul_comm]

noncomputable def smoothedProjection {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) (a : α → EuclideanSpace ℝ (Fin d)) (η : ℝ)
    (p : (Fin k → Fin d → ℝ) × (Fin k → ℝ)) : ℝ≥0∞ :=
  ∫⁻ z, boxKernel η (projectVector p.1 (a z)) p.2 ∂μ

lemma measurable_projection_kernel {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (a : α → EuclideanSpace ℝ (Fin d)) (ha : Measurable a) (η : ℝ) :
    Measurable (fun p : ((Fin k → Fin d → ℝ) × (Fin k → ℝ)) × α =>
      boxKernel η (projectVector p.1.1 (a p.2)) p.1.2) :=
  (measurable_boxKernel η).comp
    ((continuous_projectVector.measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk (ha.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_fst))

lemma measurable_smoothedProjection {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) [SFinite μ] (a : α → EuclideanSpace ℝ (Fin d))
    (ha : Measurable a) (η : ℝ) : Measurable (smoothedProjection (k := k) μ a η) :=
  (measurable_projection_kernel (k := k) (d := d) a ha η).lintegral_prod_right

lemma measurable_replicated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : ℕ}
    (f : β × α → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun x : β × (Fin m → α) => ∏ i, f (x.1,x.2 i)) := by
  apply Finset.measurable_prod
  intro i hi
  exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

lemma measurable_replica_kernel {α : Type*} [MeasurableSpace α] {k d m : ℕ}
    (a : α → EuclideanSpace ℝ (Fin d)) (ha : Measurable a) (η : ℝ) :
    Measurable (fun x : ((Fin k → Fin d → ℝ) × (Fin k → ℝ)) × (Fin m → α) =>
      ∏ i, boxKernel η (projectVector x.1.1 (a (x.2 i))) x.1.2) :=
  measurable_replicated _ (measurable_projection_kernel (k := k) (d := d) a ha η)

lemma smoothedProjection_moment_le {α : Type*} [MeasurableSpace α] {k d : ℕ}
    (μ : Measure α) [SigmaFinite μ] (hμ : μ univ ≤ 1)
    (a : α → EuclideanSpace ℝ (Fin d)) (ha : Measurable a) (hk : 0 < k)
    (p : ℕ) (M : ℝ≥0∞)
    (hcond : ∀ V : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      (V : Set (EuclideanSpace ℝ (Fin d))).Nonempty →
      Module.finrank ℝ V.direction ≤ p →
      (∫⁻ z, (ENNReal.ofReal (infDist (a z) (V : Set (EuclideanSpace ℝ (Fin d)))))⁻¹ ^ k ∂μ) ≤ M)
    (q : ℕ) (hq : q ≤ p+1) (η : ℝ) (hη : 0 < η) :
    (∫⁻ x, smoothedProjection (k := k) μ a η x ^ (q+1)
      ∂(gaussianRows k d).prod volume) ≤ ENNReal.ofReal ((2:ℝ)^(k*q))*M^q := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm := measurable_replica_kernel (k := k) (d := d) (m := q+1) a ha η
  calc
    _ = ∫⁻ x, ∫⁻ z : Fin (q+1) → α,
        ∏ i, boxKernel η (projectVector x.1 (a (z i))) x.2
        ∂Measure.pi (fun _ => μ) ∂(gaussianRows k d).prod volume := by
      apply lintegral_congr
      intro x
      exact (lintegral_pi_product μ _ ((measurable_projection_kernel (k := k) (d := d) a ha η).comp
        (measurable_const.prodMk measurable_id)) (q+1)).symm
    _ = ∫⁻ z : Fin (q+1) → α, ∫⁻ x,
        ∏ i, boxKernel η (projectVector x.1 (a (z i))) x.2
        ∂(gaussianRows k d).prod volume ∂Measure.pi (fun _ => μ) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ z : Fin (q+1) → α, ENNReal.ofReal ((2:ℝ)^(k*q)) *
        gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))
        ∂Measure.pi (fun _ => μ) := lintegral_mono fun z =>
      fixedReplica_moment_le hk η hη (fun i => a (z i))
    _ = ENNReal.ofReal ((2:ℝ)^(k*q)) * ∫⁻ z : Fin (q+1) → α,
        gramInverseProduct k (fun i : Fin q => a (z i.succ)-a (z 0))
        ∂Measure.pi (fun _ => μ) := by
      apply lintegral_const_mul
      exact (measurable_gramInverseProduct k).comp
        (Measurable.of_eval fun i => (ha.comp (measurable_pi_apply i.succ)).sub
          (ha.comp (measurable_pi_apply 0)))
    _ ≤ ENNReal.ofReal ((2:ℝ)^(k*q))*M^q := mul_le_mul_right
      (lintegral_replicaInverse_le μ hμ a ha k p M hcond q hq) _

end RepeatedLocalization

end OAI
