import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationChart
import OAI.Geometry.TamingCompatibility.Charts.ChartOverlapControl

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma concentrationDensity_compare (p q : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X,
      x ∈ tsupport (A.partition p) → x ∈ tsupport (A.partition q) →
      ∀ r : ℝ, 0 < r → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u ≤
        C*concentrationDensity A J α hs ht E q r (extChartAt Model q.val x) u+B*r^4 := by
  let K := tsupport (A.partition p) ∩ tsupport (A.partition q)
  have hK : IsCompact K := (isClosed_tsupport (A.partition p)).isCompact.inter_right (isClosed_tsupport _)
  obtain ⟨L,hL,δ,hδ,hnear⟩ := compact_chart_overlap_control p.val q.val hK
    (fun _ hx => A.subordinate p hx.1) (fun _ hx => A.subordinate q hx.2)
  obtain ⟨_,P,_,hP,hPbound⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨m,_,hm,_,hmbound⟩ := unitChartArea_bounds J α hs ht q.val
    (E q).concentrationCompact_compact (E q).concentrationCompact_target
  let M := max L 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let ε := min δ ((E q).concentrationCutoff.radius/(2*M))
  have hε : 0 < ε := lt_min hδ (div_pos (E q).concentrationCutoff.positive (by positivity))
  refine ⟨P*M^6/m,P/ε^6,by positivity,by positivity,fun x hxp hxq r hr u => ?_⟩
  have hq0 := concentrationDensity_nonneg A J α hs ht E q r (extChartAt Model q.val x) u
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · have harea : unitChartArea J α hs ht p.val u ≤ P := (hPbound u hu).2
    have hpbound : concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u ≤
        P*rationalKernel r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) := by
      rw [concentrationDensity,indicator_of_mem hu]
      exact mul_le_mul harea (cutKernel_le _ (fun z => (E p).concentrationCutoff.bump.le_one (x := z)) _ _)
        (cutKernel_nonneg _ (fun z => (E p).concentrationCutoff.bump.nonneg (x := z)) _ _) hP.le
    by_cases hz : ‖extChartAt Model p.val u.val.proj-extChartAt Model p.val x‖ ≤ ε
    · have hnv := hnear x ⟨hxp,hxq⟩ u.val.proj
        (unitChart_mem J α hs ht p.val (E p).concentrationCompact_target hu).1
        (hz.trans (min_le_left _ _))
      have hzq : ‖extChartAt Model q.val u.val.proj-extChartAt Model q.val x‖ ≤
          (E q).concentrationCutoff.radius/2 := by
        calc
          _ ≤ M*‖extChartAt Model p.val u.val.proj-extChartAt Model p.val x‖ :=
            hnv.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
          _ ≤ M*((E q).concentrationCutoff.radius/(2*M)) :=
            mul_le_mul_of_nonneg_left (hz.trans (min_le_right _ _)) hMp.le
          _ = _ := by field_simp
      have hcenter := partition_center_ball A J α ht E hE q hxq
      have hphys := (E q).concentrationCutoff.near _ hcenter
        (extChartAt Model q.val u.val.proj) (hzq.trans (by linarith [(E q).concentrationCutoff.positive]))
      have huq : u ∈ unitChartDomain J α hs ht q.val (E q).concentrationCompact :=
        ⟨extChartAt Model q.val u.val.proj,Or.inr ⟨_,hphys,rfl⟩,(extChartAt Model q.val).left_inv hnv.1⟩
      have hqa := (hmbound u huq).1
      have hqeq := concentrationDensity_near A J α hs ht E q hcenter u hnv.1 hzq r
      have hrat : rationalKernel r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) ≤
          M^6*rationalKernel r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj) := by
        apply rationalKernel_compare hr hM
        simpa only [norm_sub_rev] using hnv.2.trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      calc
        _ ≤ P*(M^6*rationalKernel r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj)) :=
          hpbound.trans (mul_le_mul_of_nonneg_left hrat hP.le)
        _ ≤ (P*M^6/m)*(unitChartArea J α hs ht q.val u *
            rationalKernel r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj)) := by
          have hpa : P*M^6 ≤ (P*M^6/m)*unitChartArea J α hs ht q.val u := by
            have hh := mul_le_mul_of_nonneg_left hqa (by positivity : 0 ≤ P*M^6/m)
            rwa [div_mul_cancel₀ _ hm.ne'] at hh
          nlinarith [mul_le_mul_of_nonneg_right hpa
            (rationalKernel_nonneg r (extChartAt Model q.val x-extChartAt Model q.val u.val.proj))]
        _ ≤ _ := by rw [←hqeq]; exact le_add_of_nonneg_right (by positivity)
    · have haway : ε ≤ ‖extChartAt Model p.val x-extChartAt Model p.val u.val.proj‖ := by
        simpa only [norm_sub_rev] using le_of_lt (lt_of_not_ge hz)
      have hh := mul_le_mul_of_nonneg_left (rationalKernel_away hε haway (r := r)) hP.le
      have he : P*(r^4/ε^6) = (P/ε^6)*r^4 := by ring
      rw [he] at hh
      exact (hpbound.trans hh).trans (le_add_of_nonneg_left (by positivity))
  · rw [concentrationDensity,indicator_of_notMem hu]
    positivity

include hE in
lemma localConcentration_compare
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (p q : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X,
      x ∈ tsupport (A.partition p) → x ∈ tsupport (A.partition q) →
      ∀ r : ℝ, 0 < r →
      localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        C*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x)+B*r^4 := by
  obtain ⟨C,B,hC,hB,hb⟩ := concentrationDensity_compare A J α hs ht E hE p q
  refine ⟨C,B,hC,hB,fun x hx hy r hr => ?_⟩
  rw [localConcentration_integral A J α hs ht E μ p hr,
    localConcentration_integral A J α hs ht E μ q hr]
  have hp := concentrationDensity_integrable A J α hs ht E μ p hr (extChartAt Model p.val x)
  have hq := concentrationDensity_integrable A J α hs ht E μ q hr (extChartAt Model q.val x)
  have hh := integral_mono hp ((hq.const_mul C).add (integrable_const (B*r^4))) (hb x hx hy r hr)
  simpa only [Pi.add_apply,integral_add (hq.const_mul C) (integrable_const (B*r^4)),integral_const_mul,integral_const,
    probReal_univ,one_smul] using hh
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

include hE in
lemma localConcentration_global_compare
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (p : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r →
      localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        C*globalConcentration A J α hs ht E μ r x+B*r^4 := by
  classical
  choose c b hc hb hh using fun q => localConcentration_compare A J α hs ht E hE μ p q
  let C := ∑ q : A.centers, c q
  let B := ∑ q : A.centers, b q
  have hC : 0 ≤ C := Finset.sum_nonneg (fun q _ => hc q)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun q _ => hb q)
  have hcC (q : A.centers) : c q ≤ C := Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ q)
  have hbB (q : A.centers) : b q ≤ B := Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ q)
  refine ⟨C,B,hC,hB,fun x hx r hr => ?_⟩
  have hq (q : A.centers) :
      A.partition q x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        C*(A.partition q x*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x))+
          A.partition q x*(B*r^4) := by
    by_cases hz : A.partition q x = 0
    · simp only [hz,zero_mul,mul_zero,add_zero,le_refl]
    · have hqx : x ∈ tsupport (A.partition q) := subset_tsupport _ (Function.mem_support.mpr hz)
      have hlocal := hh q x hx hqx r hr
      have hglobal : localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
          C*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x)+B*r^4 :=
        hlocal.trans (add_le_add
          (mul_le_mul_of_nonneg_right (hcC q) (localConcentration_nonneg A J α hs ht E μ q r _))
          (mul_le_mul_of_nonneg_right (hbB q) (by positivity)))
      have hm := mul_le_mul_of_nonneg_left hglobal (A.partition.nonneg q x)
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun q _ => hq q)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,partition_sum,one_mul] at hsum
  have he : globalConcentration A J α hs ht E μ r x =
      ∑ q : A.centers, A.partition q x*localConcentration A J α hs ht E μ q r (extChartAt Model q.val x) := by
    simp only [globalConcentration,Finset.sum_apply,concentrationPatch_apply]
  rwa [←he] at hsum
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
