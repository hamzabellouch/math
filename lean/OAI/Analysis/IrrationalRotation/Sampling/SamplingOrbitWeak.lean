import OAI.Analysis.IrrationalRotation.Sampling.SamplingCylinderError
import OAI.Analysis.IrrationalRotation.Product.ProductOrbitTests

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductModel.TailTrimming
open SamplingCylinderWeak

def cylinderTestAverage (θ : ℕ → ℝ) (N : Finset ℕ) (w : ℕ → Base → ℝ)
    (t : CylinderTest (Bool × ℕ)) (x : Base) : ℝ :=
  (N.card : ℝ)⁻¹ * ∑ n ∈ N, orbitTestWeight θ (endpointCylinder t) w n x

theorem cylinderTestAverage_nonneg (θ : ℕ → ℝ) (N : Finset ℕ) (w : ℕ → Base → ℝ)
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x) (t : CylinderTest (Bool × ℕ)) (x : Base) :
    0 ≤ cylinderTestAverage θ N w t x :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun n hn => orbitTestWeight_nonneg θ _ w n (hw0 n hn) x)

@[simp] theorem cylinderTestAverage_empty (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (x : Base) :
    cylinderTestAverage θ N w ∅ x = (N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x := by
  simp [cylinderTestAverage, orbitTestWeight, endpointCylinder]

theorem orbitAverage_finite_of_memLp_average (θ : ℕ → ℝ) (N : Finset ℕ)
    (w : ℕ → Base → ℝ) (hw : ∀ n ∈ N, Measurable (w n))
    (hw0 : ∀ n ∈ N, ∀ x, 0 ≤ w n x)
    (havg : MemLp (fun x => (N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x) 2 baseMeasure) :
    IsFiniteMeasure (orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))) := by
  let a : Base → ℝ := fun x => (N.card : ℝ)⁻¹ * ∑ n ∈ N, w n x
  have ha0 : 0 ≤ᵐ[baseMeasure] a := Filter.Eventually.of_forall fun x =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun n hn => hw0 n hn x)
  have ha : Integrable a baseMeasure := havg.integrable (by norm_num)
  have hfinite : IsFiniteMeasure (baseMeasure.withDensity (fun x => ENNReal.ofReal (a x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal ha ha0]
    exact ENNReal.ofReal_lt_top
  have hmap : IsFiniteMeasure
      ((orbitAverageMeasure θ N (fun n x => ENNReal.ofReal (w n x))).map Prod.fst) := by
    rw [orbitAverageMeasure_first_marginal_real θ N w hw hw0]
    exact hfinite
  let := hmap
  exact Measure.isFiniteMeasure_of_map measurable_fst.aemeasurable

theorem orbitAverage_weaklyConverges_of_tested_L2
    (θ : ℕ → ℝ) (N : ℕ → Finset ℕ) (w : ℕ → ℕ → Base → ℝ)
    (hw : ∀ l, ∀ n ∈ N l, Measurable (w l n))
    (hw0 : ∀ l, ∀ n ∈ N l, ∀ x, 0 ≤ w l n x)
    (g : CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hf : ∀ t l, MemLp (cylinderTestAverage θ (N l) (w l) t) 2 baseMeasure)
    (hg : ∀ t l, MemLp (g t l) 2 baseMeasure)
    {ν : Measure EndpointPair} (hν : IsFiniteMeasure ν)
    (herror : ∀ t, Tendsto (fun l => eLpNorm
      (fun x => cylinderTestAverage θ (N l) (w l) t x - g t l x) 2 baseMeasure)
      atTop (𝓝 0))
    (hideal : ∀ t, Tendsto (fun l => ∫ x, g t l x ∂baseMeasure) atTop
      (𝓝 (ν.real (endpointCylinder t)))) :
    WeaklyConverges
      (fun l => orbitAverageMeasure θ (N l) (fun n x => ENNReal.ofReal (w l n x))) ν := by
  have hfinite (l : ℕ) : IsFiniteMeasure
      (orbitAverageMeasure θ (N l) (fun n x => ENNReal.ofReal (w l n x))) := by
    apply orbitAverage_finite_of_memLp_average θ (N l) (w l) (hw l) (hw0 l)
    have heq : cylinderTestAverage θ (N l) (w l) ∅ =
        (fun x => ((N l).card : ℝ)⁻¹ * ∑ n ∈ N l, w l n x) :=
      funext (cylinderTestAverage_empty θ (N l) (w l))
    rw [← heq]
    exact hf ∅ l
  refine weaklyConverges_of_tested_first_marginal_L2 hfinite hν
    (fun t l => cylinderTestAverage θ (N l) (w l) t) g hf hg ?_ ?_ herror hideal
  · intro t l
    exact Filter.Eventually.of_forall (cylinderTestAverage_nonneg θ (N l) (w l) (hw0 l) t)
  · intro t l
    exact orbitAverageMeasure_restrict_first_marginal_real θ (N l) (w l) (hw l) (hw0 l)
      (endpointCylinder t) (endpointCylinder_measurable t)

theorem ae_all_triangular_orbitAverage_weaklyConverges_of_tested_L2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (θ : Ω → ℕ → ℝ) (N : ℕ → Finset ℕ)
    (w : Finset ℕ → Ω → ℕ → ℕ → Base → ℝ)
    (hw : ∀ I ω l, ∀ n ∈ N l, Measurable (w I ω l n))
    (hw0 : ∀ I ω l, ∀ n ∈ N l, ∀ x, 0 ≤ w I ω l n x)
    (g : Finset ℕ → CylinderTest (Bool × ℕ) → ℕ → Base → ℝ)
    (hf : ∀ I ω t l, MemLp (cylinderTestAverage (θ ω) (N l) (w I ω l) t) 2 baseMeasure)
    (hg : ∀ I t l, MemLp (g I t l) 2 baseMeasure)
    (herror : ∀ I t, ∀ᵐ ω ∂P, Tendsto (fun l => eLpNorm
      (fun x => cylinderTestAverage (θ ω) (N l) (w I ω l) t x - g I t l x)
      2 baseMeasure) atTop (𝓝 0))
    (hideal : ∀ I t, Tendsto (fun l => ∫ x, g I t l x ∂baseMeasure) atTop
      (𝓝 ((triangularLaw I).real (endpointCylinder t)))) :
    ∀ᵐ ω ∂P, ∀ I, WeaklyConverges
      (fun l => orbitAverageMeasure (θ ω) (N l)
        (fun n x => ENNReal.ofReal (w I ω l n x))) (triangularLaw I) := by
  have hall : ∀ᵐ ω ∂P, ∀ I t, Tendsto (fun l => eLpNorm
      (fun x => cylinderTestAverage (θ ω) (N l) (w I ω l) t x - g I t l x)
      2 baseMeasure) atTop (𝓝 0) :=
    ae_all_iff.mpr fun I => ae_all_iff.mpr (herror I)
  filter_upwards [hall] with ω hω
  intro I
  have hν : IsFiniteMeasure (triangularLaw I) := by unfold triangularLaw; infer_instance
  exact orbitAverage_weaklyConverges_of_tested_L2 (θ ω) N (w I ω) (hw I ω) (hw0 I ω)
    (g I) (hf I ω) (hg I) hν (hω I) (hideal I)

end Invariant233.ProductModel.TailTrimming

end

end OAI
