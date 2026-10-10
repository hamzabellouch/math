import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestAlmostSure
import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingRectangles
import OAI.Analysis.IrrationalRotation.Product.ProductIdealCylinderLimit
import OAI.Analysis.IrrationalRotation.Analysis.SquaredIntegralLp

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel.SamplingWeights
open SamplingCylinderWeak

theorem eventually_finset_subset_sourcePrefix {p : ProductScaleData}
    (hp : ProductScaleLaws p) (I : Finset ℕ) :
    ∀ᶠ l in atTop, I ⊆ Finset.range (p.prefixCount (l + 1)) := by
  have hcount (l : ℕ) : l ≤ p.prefixCount l := by
    calc
      l = ∑ _i ∈ Finset.range l, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range l, p.m i :=
        Finset.sum_le_sum (fun i _ => hp.m_pos i)
  change ∀ᶠ l in atTop, ∀ i ∈ I, i ∈ Finset.range (p.prefixCount (l + 1))
  rw [Finset.eventually_all]
  intro i _hi
  filter_upwards [eventually_ge_atTop i] with l hl
  exact Finset.mem_range.mpr (lt_of_le_of_lt hl
    (lt_of_lt_of_le (Nat.lt_succ_self l) (hcount (l + 1))))

theorem memLp_cylinderTestAverage (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ)
    (t : CylinderTest (Bool × ℕ)) :
    MemLp (TailTrimming.cylinderTestAverage θ N (orbitWeight D I h α θ) t)
      2 baseMeasure := by
  unfold TailTrimming.cylinderTestAverage
  apply MemLp.const_mul
  apply memLp_finsetSum N
  intro n _hn
  exact (memLp_orbitWeight D I hh hα θ n 2).indicator
    ((TailTrimming.measurable_orbitPairMap θ n) (endpointCylinder_measurable t))

theorem source_orbitAverage_weaklyConverges_of_cylinder_energy
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (θ : ℕ → ℝ) (I : Finset ℕ)
    (herror : ∀ t : CylinderTest (Bool × ℕ), Tendsto
      (fun l => ∫ x, (sourceTestedError p N false I
        (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) l θ x) ^ 2
        ∂baseMeasure) atTop (𝓝 0)) :
    WeaklyConverges
      (fun l => TailTrimming.orbitAverageMeasure θ (N l)
        (fun n x => ENNReal.ofReal (orbitWeight
          (Finset.range (p.prefixCount (l + 1))) I
          ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2) θ n x)))
      (triangularLaw I) := by
  let D : ℕ → Finset ℕ := fun l => Finset.range (p.prefixCount (l + 1))
  let h : ℕ → ℝ := fun l => (p.m l : ℝ) ^ (-(3 / 5 : ℝ))
  let α : ℕ → ℝ := fun l => 1 / (p.m l : ℝ) ^ 2
  let w : ℕ → ℕ → Base → ℝ := fun l => orbitWeight (D l) I (h l) (α l) θ
  let g : CylinderTest (Bool × ℕ) → ℕ → Base → ℝ := fun t l =>
    testedIdeal false (D l) I (h l) (α l)
      (cylinderCoordinateSet t false) (cylinderCoordinateSet t true)
  have hm (l : ℕ) : 0 < (p.m l : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 100) (hp.m_ge_100 l))
  have hh (l : ℕ) : 0 < h l := Real.rpow_pos_of_pos (hm l) _
  have hα (l : ℕ) : 0 < α l := one_div_pos.mpr (sq_pos_of_pos (hm l))
  have hh1 (l : ℕ) : h l ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 100) (hp.m_ge_100 l))
    · norm_num
  have hf (t : CylinderTest (Bool × ℕ)) (l : ℕ) :
      MemLp (TailTrimming.cylinderTestAverage θ (N l) (w l) t) 2 baseMeasure :=
    memLp_cylinderTestAverage (D l) I (N l) (hh l) (hα l) θ t
  have hg (t : CylinderTest (Bool × ℕ)) (l : ℕ) : MemLp (g t l) 2 baseMeasure :=
    memLp_testedIdeal false (D l) I (hh l) (hα l) _ _
      (fun i _ => measurableSet_cylinderCoordinateSet t false i)
      (fun i _ => measurableSet_cylinderCoordinateSet t true i) 2
  apply TailTrimming.orbitAverage_weaklyConverges_of_tested_L2 θ N w
    (fun l n _ => measurable_orbitWeight (D l) I (h l) (α l) θ n)
    (fun l n _ x => (orbitWeight_bounds (D l) I (hh l) (hα l) θ n x).1)
    g hf hg (Sampling.triangularLaw_finite I)
  · intro t
    have he : Tendsto (fun l => ∫ x,
        (TailTrimming.cylinderTestAverage θ (N l) (w l) t x - g t l x) ^ 2
          ∂baseMeasure) atTop (𝓝 0) := by
      apply (herror t).congr'
      filter_upwards [eventually_cylinderSupport_subset_sourcePrefix hp t] with l hD
      congr 1
      funext x
      rw [cylinderTestAverage_eq_product_average (D l) I (N l) (h l) (α l) θ t hD]
      rfl
    have hn := SquaredIntegralLp.tendsto_eLpNorm_two_of_integral_sq
      baseMeasure baseMeasure
      (fun l x => TailTrimming.cylinderTestAverage θ (N l) (w l) t x - g t l x)
      (fun _ : Base => (0 : ℝ))
      (fun index => ((hf t index).sub (hg t index)).aestronglyMeasurable)
      aestronglyMeasurable_const
      (fun l => ((hf t l).sub (hg t l)).integrable_sq)
      (by simp) (by simpa using he)
    simpa using hn
  · intro t
    apply (IdealSampling.law_cylinder_real_tendsto_of_productScaleLaws I hp t).congr'
    filter_upwards [eventually_finset_subset_sourcePrefix hp I,
      eventually_cylinderSupport_subset_sourcePrefix hp t] with l hI hD
    exact idealLaw_real_cylinder_eq_integral hI (hh l) (hh1 l) (hα l) t hD

theorem ae_all_source_orbitAverage_weaklyConverges_of_cylinder_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) (θ : Ω → ℕ → ℝ)
    (herror : ∀ (I : Finset ℕ) (t : CylinderTest (Bool × ℕ)), ∀ᵐ ω ∂P,
      Tendsto (fun l => ∫ x, (sourceTestedError p N false I
        (cylinderCoordinateSet t false) (cylinderCoordinateSet t true) l (θ ω) x) ^ 2
        ∂baseMeasure) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ I, WeaklyConverges
      (fun l => TailTrimming.orbitAverageMeasure (θ ω) (N l)
        (fun n x => ENNReal.ofReal (orbitWeight
          (Finset.range (p.prefixCount (l + 1))) I
          ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2) (θ ω) n x)))
      (triangularLaw I) := by
  have hall := ae_all_iff.mpr fun I => ae_all_iff.mpr (herror I)
  filter_upwards [hall] with ω hω
  intro I
  exact source_orbitAverage_weaklyConverges_of_cylinder_energy hp N (θ ω) I (hω I)

end Invariant233.ProductModel.SamplingWeights

end

end OAI
