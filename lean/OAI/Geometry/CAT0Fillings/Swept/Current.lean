import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.GeneralPush
import OAI.Geometry.CAT0Fillings.Radial.MassComparison
import OAI.Geometry.CAT0Fillings.Slicing.IntegralBoundary
import OAI.Geometry.CAT0Fillings.Swept.WholeMass

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

structure ChartGeometry {T : Functional X k} (hT : IsMetricCurrent T) where
  chart : ℕ → IntegerChart X k
  field : ℕ → Euc k → Seminorm ℝ (Euc k)
  disjoint : Pairwise (fun i j => Disjoint (chart i).image (chart j).image)
  summable : Summable (fun i => mass (chart i).action)
  action : ∀ b π, T b π = ∑' i, (chart i).action b π
  measurable : ∀ i v, Measurable (fun z => field i z v)
  differential : ∀ i, ∀ᵐ z ∂volume.restrict (chart i).domain,
    (∀ hz : z ∈ (chart i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
      (chart i).domain (chart i).param (field i z) ⟨z,hz⟩) ∧
    (∀ u v, field i z (u+v)^2+field i z (u-v)^2 = 2*field i z u^2+2*field i z v^2) ∧
    (∀ v, field i z v = 0 ↔ v = 0)
  integrable : ∀ i, Integrable (fun z => |((chart i).multiplicity z : ℝ)| *Real.sqrt
    (polarizationMatrix (field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
    (volume.restrict (chart i).domain)
  chart_mass : ∀ i, mass (chart i).action = ∫ z, |((chart i).multiplicity z : ℝ)| *Real.sqrt
    (polarizationMatrix (field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
    ∂volume.restrict (chart i).domain
  measure_eq : MassMeasure.currentMassMeasure hT = Measure.sum (fun i =>
    (chart i).majorantMeasure (fun z => Real.sqrt
      (polarizationMatrix (field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det))
  total_mass : mass T = ∑' i, mass (chart i).action
  current : ∀ i, IsMetricCurrent (chart i).action
  control : ∀ i, Controls (chart i).action ((chart i).majorantMeasure (fun z =>
    Real.sqrt (polarizationMatrix (field i z)
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det))

theorem exists_chartGeometry {T : Functional X k}
    (hX : IsCAT0 X) (hT : IsMetricCurrent T) (hr : IntegerRectifiable T) :
    Nonempty (ChartGeometry hT) := by
  classical
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hr
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
  exact ⟨⟨C,p,hdis,hsum,heq,hpm,hp,hρ,hmass,hmeasure,htotal,hC,hcontrol⟩⟩

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def gram (i : ℕ) (z : Euc k) : Matrix (Fin k) (Fin k) ℝ :=
  polarizationMatrix (q.field i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
noncomputable def density (i : ℕ) (z : Euc k) : ℝ :=
  |((q.chart i).multiplicity z : ℝ)| *Real.sqrt (q.gram i z).det

lemma density_integrable (i : ℕ) : Integrable (q.density i)
    (volume.restrict (q.chart i).domain) := q.integrable i
lemma density_summable : Summable (fun i => ∫ z, q.density i z
    ∂volume.restrict (q.chart i).domain) := by
  simpa only [density,gram,q.chart_mass] using q.summable
lemma density_mass : mass T = ∑' i, ∫ z, q.density i z
    ∂volume.restrict (q.chart i).domain := by
  simpa only [density,gram,q.chart_mass] using q.total_mass

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma endpoint_lipschitz [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
    (t : Icc (0:ℝ) 1) :
    LipschitzWith 1 (fun y : X => (t,y) : X → ClosedCylinder X) := by
  simpa using (LipschitzWith.const t).prodMk
    (LipschitzWith.id : LipschitzWith 1 (id : X → X))

theorem swept_boundary_integral
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (C : ℕ → IntegerChart X (k+1))
    (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (F : ClosedCylinder X → X) {K : ℝ≥0} (hF : LipschitzWith K F)
    (hF0 : ∀ y, F (⟨0,by constructor <;> norm_num⟩,y) = y) :
    IsIntegral (k+2) (pushCurrent F (closedPrismFamily C)) ∧
    boundarySucc (pushCurrent F (closedPrismFamily C)) =
      pushCurrent (fun y => F (⟨1,by constructor <;> norm_num⟩,y)) T - T := by
  let f : X → X := fun y => F (⟨1,by constructor <;> norm_num⟩,y)
  have hf : LipschitzWith K f := by
    simpa only [mul_one,Function.comp_def,f] using
      hF.comp (endpoint_lipschitz (X := X) ⟨1,by constructor <;> norm_num⟩)
  let : Nonempty (ClosedCylinder X) := ⟨(⟨0,by constructor <;> norm_num⟩,Classical.choice inferInstance)⟩
  have hb : boundarySucc (pushCurrent F (closedPrismFamily C)) = pushCurrent f T - T := by
    funext b π
    by_cases hab : Admissible b π
    · rw [pushCurrent_boundarySucc _ hF,pushCurrent_apply _ _ hab,
        closedPrismFamily_boundary_cycle hT.1 hT.2.1 hz C hs heq _ _
          (admissible_comp hab hF)]
      simp only [Pi.sub_apply,pushCurrent_apply _ _ hab,Function.comp_apply,hF0,f]
      rfl
    · simp only [boundarySucc,Pi.sub_apply,pushCurrent,ite_eq_right hab,
        hT.1.offDomain b π hab,sub_self]
  have hbi := (integral_push hT hf).sub hT
  refine ⟨⟨pushCurrent_isMetricCurrent (closedPrismFamily_current C hs) hF,
    integerRectifiable_push (closedPrismFamily_rectifiable C hd hs) hF,?_,?_⟩,hb⟩
  · rw [hb]; exact hbi.1
  · rw [hb]; exact hbi.2.1

end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def sweptMass (o : X) (g : X → ℝ) : ℝ :=
  ∑' i, ∫ z, |((q.chart i).multiplicity z : ℝ)| *(q.chart i).sweptWeight (q.field i) o g z
    ∂volume.restrict (q.chart i).domain

lemma swept_integrable_summable (o : X) {g : X → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg0 : ∀ y, 0 ≤ g y) :
    (∀ i, Integrable (fun z => |((q.chart i).multiplicity z : ℝ)| *
      (q.chart i).sweptWeight (q.field i) o g z)
      (volume.restrict (q.chart i).domain)) ∧
    Summable (fun i => ∫ z, |((q.chart i).multiplicity z : ℝ)| *
      (q.chart i).sweptWeight (q.field i) o g z ∂volume.restrict (q.chart i).domain) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((continuous_const.dist continuous_id).mul hg.continuous).continuousOn
  apply summable_swept_integrals q.chart q.field q.measurable q.differential q.integrable
    q.density_summable o hg hg0
  intro y
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,Pi.mul_apply,id_eq] using hB y (mem_univ y))

lemma sweptMass_nonneg (o : X) {g : X → ℝ} (hg0 : ∀ y, 0 ≤ g y) :
    0 ≤ q.sweptMass o g := by
  apply tsum_nonneg
  intro i
  apply integral_nonneg_of_ae
  filter_upwards [(q.chart i).ae_sweptWeight_nonneg (q.field i) o hg0] with z hz
  exact mul_nonneg (abs_nonneg _) hz

lemma sweptMass_const_mul (o : X) (g : X → ℝ) (h : ℝ) :
    q.sweptMass o (fun y => h*g y) = h*q.sweptMass o g := by
  have hs (C : IntegerChart X k) : C.scalar (fun y => h*g y) = fun z => h*C.scalar g z := by
    funext z
    by_cases hz : z ∈ C.domain <;> simp [IntegerChart.scalar,hz]
  simp only [sweptMass,IntegerChart.sweptWeight,hs]
  simp_rw [show ∀ (a b c d e : ℝ), a*(b*(h*c)*d*e) = h*(a*(b*c*d*e)) by intros; ring]
  simp only [integral_const_mul,tsum_mul_left]

end ChartGeometry

theorem exists_swept_current {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) (q : ChartGeometry hT.1)
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (hseg1 : ∀ o x, seg o x 1 = x)
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧
      boundarySucc S = pushCurrent (fun y => seg o y (1-g y)) T - T ∧
      mass S ≤ q.sweptMass o g := by
  obtain ⟨F,⟨L,hF⟩,hFeq,hFcl⟩ := exists_swept_radial_map seg hseg hcomp o hg hg0 hg1
  have hF0 : ∀ y, F (⟨0,by constructor <;> norm_num⟩,y) = y := by
    intro y
    rw [hFeq]
    simp only [zero_mul,sub_zero,hseg1]
  obtain ⟨hS,hb⟩ := swept_boundary_integral hT hz q.chart q.disjoint q.summable q.action F hF hF0
  obtain ⟨hI,hIs⟩ := q.swept_integrable_summable o hg hg0
  refine ⟨pushCurrent F (closedPrismFamily q.chart),hS,?_,?_⟩
  · simpa only [hFeq,one_mul] using hb
  · exact whole_swept_mass_le q.chart q.summable seg hcomp o g hg hg0 hg1 F hF hFcl
      q.field hI hIs q.differential

end CAT0Fillings
end

end OAI
