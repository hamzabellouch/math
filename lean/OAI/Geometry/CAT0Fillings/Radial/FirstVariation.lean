import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.WholeMass
import OAI.Geometry.CAT0Fillings.Radial.SeriesDerivative

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix CurrentOperations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ}
theorem exists_whole_radial_first_variation {T : Functional X k}
    (hX : IsCAT0 X) (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T)
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∃ (C : ℕ → IntegerChart X k) (p : ℕ → Euc k → Seminorm ℝ (Euc k)),
      Pairwise (fun i j => Disjoint (C i).image (C j).image) ∧
      (∀ b π, T b π = ∑' i, (C i).action b π) ∧
      (∀ i v, Measurable (fun z => p i z v)) ∧
      (∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
        (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
          (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
        (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
        (∀ v, p i z v = 0 ↔ v = 0)) ∧
      mass T = (∑' i, ∫ z, |((C i).multiplicity z : ℝ)| *Real.sqrt
        (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
          ∂volume.restrict (C i).domain) ∧
      (let d : ℕ → ℝ := fun i => ∫ z,
      (|((C i).multiplicity z : ℝ)| * Real.sqrt
        (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) *
      -((k:ℝ)*(C i).scalar g z+(C i).scalar (dist o) z *
        (differentialRow (fderivWithin ℝ ((C i).scalar (dist o)) (C i).domain z) ⬝ᵥ
          (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ ((C i).scalar g) (C i).domain z))))
      ∂volume.restrict (C i).domain
    Summable d ∧ HasDerivWithinAt
      (fun t => ∑' i, ∫ z, |((C i).multiplicity z : ℝ)| * (C i).radialJacobian
        (fun z => polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z ∂volume.restrict (C i).domain) (∑' i, d i) (Ici 0) 0) ∧
      ∀ t ∈ Icc (0:ℝ) 1, (∀ y, 1-t*g y ∈ Icc (0:ℝ) 1) →
        Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *(C i).radialJacobian
          (fun z => polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z ∂volume.restrict (C i).domain) ∧
        mass (pushCurrent (fun y => seg o y (1-t*g y)) T) ≤
          ∑' i, ∫ z, |((C i).multiplicity z : ℝ)| *(C i).radialJacobian
            (fun z => polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
            o g t z ∂volume.restrict (C i).domain := by
  classical
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hrect
  choose P hPm hP hρ hfin hcontrol hmin hfield using
    fun i => (C i).exists_exact_quadratic_mass hX (hC i)
  choose p hPeq hpm hp using hfield
  simp only [hPeq] at hρ hfin hcontrol hmin
  let J (i : ℕ) (z : Euc k) := Real.sqrt
    (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
  have hmass (i : ℕ) : mass (C i).action =
      ∫ z, |((C i).multiplicity z : ℝ)| *J i z ∂volume.restrict (C i).domain :=
    (C i).mass_eq_integral_majorant (hC i) (hρ i)
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _) (hcontrol i) (hmin i)
  let μ (i : ℕ) : Measure X := (C i).majorantMeasure (J i)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := hfin
  let := hμfin
  have htot (i : ℕ) : (μ i).real univ = mass (C i).action := by
    have heqm : MassMeasure.currentMassMeasure (hC i) = μ i := by
      apply le_antisymm (MassMeasure.currentMassMeasure_le (hC i) (hcontrol i))
      exact hmin i _ inferInstance (MassMeasure.currentMassMeasure_controls (hC i))
    rw [←heqm]
    exact MassMeasure.currentMassMeasure_total _
  have hμsum : Summable (fun i => (μ i).real univ) := by simpa only [htot] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  have hmeasure : MassMeasure.currentMassMeasure hT = Measure.sum μ := by
    apply le_antisymm
    · exact MassMeasure.currentMassMeasure_le hT (controls_sum_general hcontrol heq)
    · exact sum_measure_le_of_component_minimal hC hcontrol hmin heq
        (fun i => (C i).measurableSet_image) hdis
        (fun i => (C i).majorantMeasure_ae_image _) (MassMeasure.currentMassMeasure_controls hT)
  have htotal : mass T = ∑' i, mass (C i).action := by
    rw [←MassMeasure.currentMassMeasure_total hT,hmeasure]
    rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.tsum_toReal_eq (fun i => measure_ne_top (μ i) univ)]
    exact tsum_congr htot
  refine ⟨C,p,hdis,heq,hpm,hp,?_,?_,?_⟩
  · simpa only [hmass,J] using htotal
  · exact countable_chart_radial_first_variation C p hpm hp hρ
      (by simpa only [hmass,J] using hsum) o hg
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  obtain ⟨A,hA,hbound⟩ := uniform_chart_radialJacobian_majorant (k := k) o hg hB hK hgb hrb
  intro t ht htg
  let R (i : ℕ) (z : Euc k) := (C i).radialJacobian
    (fun z => polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) o g t z
  let I (i : ℕ) : ℝ := ∫ z, |((C i).multiplicity z : ℝ)| *R i z
    ∂volume.restrict (C i).domain
  have hrad (i : ℕ) : Integrable (fun z => |((C i).multiplicity z : ℝ)| *R i z)
      (volume.restrict (C i).domain) :=
    (C i).integrable_radialJacobian (p i) (hpm i) (hp i) (hρ i) o hg hB hK hgb hrb ht
  have hI0 (i : ℕ) : 0 ≤ I i := integral_nonneg fun z =>
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hIle (i : ℕ) : I i ≤ A*mass (C i).action := by
    rw [hmass,←integral_const_mul]
    apply integral_mono_ae (hrad i) ((hρ i).const_mul A)
    filter_upwards [hbound (C i) (p i) (hp i) t ht] with z hz
    calc
      _ ≤ |((C i).multiplicity z : ℝ)| *(A*J i z) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by ring
  have hIsum : Summable I := (hsum.mul_left A).of_nonneg_of_le hI0 hIle
  obtain ⟨L,hf⟩ := radial_lipschitzWith seg hseg hcomp o hg t htg
  let f : X → X := fun y => seg o y (1-t*g y)
  have hpush (i : ℕ) : IsMetricCurrent (pushCurrent f (C i).action) :=
    pushCurrent_isMetricCurrent (hC i) hf
  have hpushle (i : ℕ) : mass (pushCurrent f (C i).action) ≤ I i :=
    (C i).radial_push_mass_le seg hcomp o g hg t htg hf (p i) (hp i) (hrad i)
  have hpushsum : Summable (fun i => mass (pushCurrent f (C i).action)) :=
    hIsum.of_nonneg_of_le (fun i => mass_nonneg _) hpushle
  have hpusheq : pushCurrent f T = fun b π => ∑' i, pushCurrent f (C i).action b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [pushCurrent_apply _ _ hab]
      exact heq _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  refine ⟨hIsum,?_⟩
  change mass (pushCurrent f T) ≤ ∑' i, I i
  rw [hpusheq]
  exact (mass_tsum_le hpush hpushsum).trans (hpushsum.tsum_le_tsum hpushle hIsum)
end CAT0Fillings

end

end

end OAI
