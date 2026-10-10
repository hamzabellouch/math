import Mathlib
import OAI.Geometry.CAT0Fillings.Radial.WholeMass
import OAI.Geometry.CAT0Fillings.Radial.SeriesDerivative
import OAI.Geometry.CAT0Fillings.Calculus.AbsoluteValue
import OAI.Geometry.CAT0Fillings.Calculus.ChainSet

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma nonnegative_mem_closed (hz : IsCycle T) {S : Set q.Sobolev} (hS : IsClosed S)
    (hmem : ∀ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u),
      (∀ x, 0 ≤ u x) → q.lipSobolev hu ∈ S)
    (P : q.Sobolev) (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x) :
    P ∈ S := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hepos (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (t : ℝ) : abs (t/|t|) ≤ 1 := by
    rw [abs_div,abs_abs]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_self (abs_pos.mpr ht).ne']
  obtain ⟨Q,hQS,hQ,_⟩ := q.closed_chain_uniform_in_closed (F := abs) (D := fun t => t/|t|)
    (show LipschitzWith 1 abs from LipschitzWith.of_dist_le_mul (fun x y => by simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y))
    (measurable_id.div measurable_id.abs) (by norm_num : (0:ℝ) ≤ 1) hb
    (fun j => absApprox (e j)) (fun j => absApproxDeriv (e j)) (fun _ => 1)
    (fun j => absApprox_lipschitz (hepos j)) (fun j => absApprox_hasDerivAt (hepos j))
    (fun j => continuous_absApproxDeriv (hepos j)) (fun j => absApproxDeriv_bound (hepos j))
    (absApproxDeriv_tendsto he hepos) e he (fun j => absApprox_error (hepos j).le) P hS
    (fun j u K hu => hmem _ _ _ (fun x => Real.sqrt_nonneg _))
  have hQP : Q = P := q.inclusion_injective hz (Lp.ext (by
    filter_upwards [hQ,hP] with x hx hp
    exact hx.trans (abs_of_nonneg hp)))
  rwa [hQP] at hQS

lemma nonnegative_linear_inequality (hz : IsCycle T) (L : q.Sobolev →L[ℝ] ℝ)
    (hL : ∀ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u),
      (∀ x, 0 ≤ u x) → L (q.lipSobolev hu) ≤ 0)
    (P : q.Sobolev) (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x) :
    L P ≤ 0 :=
  q.nonnegative_mem_closed hz (isClosed_le L.continuous continuous_const) hL P hP
end CAT0Fillings.ChartGeometry
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

noncomputable def spatialMass (o : X) (g : X → ℝ) (t : ℝ) : ℝ :=
  ∑' i, ∫ z, |((q.chart i).multiplicity z : ℝ)| *
    (q.chart i).radialJacobian (q.gram i) o g t z ∂volume.restrict (q.chart i).domain

noncomputable def radialVariationChart (o : X) (g : X → ℝ) (i : ℕ) : ℝ :=
  ∫ z, q.density i z * ((k:ℝ)*(q.chart i).scalar g z + (q.chart i).scalar (dist o) z *
    (differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z) ⬝ᵥ
      (q.gram i z)⁻¹.mulVec
        (differentialRow (fderivWithin ℝ ((q.chart i).scalar g) (q.chart i).domain z))))
  ∂volume.restrict (q.chart i).domain

noncomputable def radialVariation (o : X) (g : X → ℝ) : ℝ := ∑' i, q.radialVariationChart o g i

lemma spatialMass_zero (o : X) (g : X → ℝ) : q.spatialMass o g 0 = mass T := by
  rw [q.density_mass]
  apply tsum_congr
  intro i
  simp only [density,IntegerChart.radialJacobian,metricSpatialRadialForm]
  simp

lemma spatialMass_nonneg (o : X) (g : X → ℝ) (t : ℝ) : 0 ≤ q.spatialMass o g t := by
  apply tsum_nonneg
  intro i
  exact integral_nonneg fun z => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

lemma spatialMass_first_variation (o : X) {g : X → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    Summable (q.radialVariationChart o g) ∧
    HasDerivWithinAt (q.spatialMass o g) (-q.radialVariation o g) (Ici 0) 0 := by
  have hh := countable_chart_radial_first_variation q.chart q.field q.measurable q.differential
    q.integrable q.density_summable o hg
  dsimp only at hh
  simp_rw [mul_neg,integral_neg,tsum_neg] at hh
  refine ⟨?_,hh.2⟩
  have hs := hh.1.neg
  change Summable (fun i => -(-q.radialVariationChart o g i)) at hs
  simpa only [neg_neg] using hs

lemma spatial_push_mass_le
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1) :
    mass (pushCurrent (fun y => seg o y (1-t*g y)) T) ≤ q.spatialMass o g t := by
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
  let I (i : ℕ) : ℝ := ∫ z, |((q.chart i).multiplicity z : ℝ)| *
    (q.chart i).radialJacobian (q.gram i) o g t z ∂volume.restrict (q.chart i).domain
  have hrad (i : ℕ) : Integrable (fun z => |((q.chart i).multiplicity z : ℝ)| *
      (q.chart i).radialJacobian (q.gram i) o g t z) (volume.restrict (q.chart i).domain) :=
    (q.chart i).integrable_radialJacobian (q.field i) (q.measurable i) (q.differential i)
      (q.integrable i) o hg hB hK hgb hrb ht
  have hI0 (i : ℕ) : 0 ≤ I i := integral_nonneg fun z =>
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hIle (i : ℕ) : I i ≤ A*mass (q.chart i).action := by
    rw [q.chart_mass,←integral_const_mul]
    apply integral_mono_ae (hrad i) ((q.integrable i).const_mul A)
    filter_upwards [hbound (q.chart i) (q.field i) (q.differential i) t ht] with z hz
    calc
      _ ≤ |((q.chart i).multiplicity z : ℝ)| *(A*Real.sqrt (q.gram i z).det) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by dsimp only [gram]; ring
  have hIsum : Summable I := (q.summable.mul_left A).of_nonneg_of_le hI0 hIle
  obtain ⟨L,hf⟩ := radial_lipschitzWith seg hseg hcomp o hg t htg
  let f : X → X := fun y => seg o y (1-t*g y)
  have hpush (i : ℕ) : IsMetricCurrent (pushCurrent f (q.chart i).action) :=
    pushCurrent_isMetricCurrent (q.chart i).action_isMetricCurrent hf
  have hpushle (i : ℕ) : mass (pushCurrent f (q.chart i).action) ≤ I i :=
    (q.chart i).radial_push_mass_le seg hcomp o g hg t htg hf (q.field i) (q.differential i) (hrad i)
  have hpushsum : Summable (fun i => mass (pushCurrent f (q.chart i).action)) :=
    hIsum.of_nonneg_of_le (fun i => mass_nonneg _) hpushle
  have hpusheq : pushCurrent f T = fun b π => ∑' i, pushCurrent f (q.chart i).action b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [pushCurrent_apply _ _ hab]
      exact q.action _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  change mass (pushCurrent f T) ≤ ∑' i, I i
  rw [hpusheq]
  exact (mass_tsum_le hpush hpushsum).trans (hpushsum.tsum_le_tsum hpushle hIsum)

end ChartGeometry
end CAT0Fillings
end

end OAI
