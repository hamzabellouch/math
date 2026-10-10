import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.NumberTheory.Jacobsthal.Analysis.LiteralCompactRemoval
import OAI.NumberTheory.Jacobsthal.Renewal.RetainedOccupationLimit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OriginalPrimeOccupationLimit

open _root_.Set _root_.Filter
open scoped Topology
open FinitePathGeometry PrimeHistories PrimeBinMembership
open LiteralPrimeOccupation LiteralCompactRemoval RetainedOccupationLimit
open CompactLogOccupationTest NormalizedOccupationLimit

theorem original_prime_continuous_occupation_limit {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |uncappedFamilyValue H w ell start-invariantAverage (arrivalTest ell H)| ≤ ε := by
  obtain ⟨BP,wP,hBP,hwP,hretained⟩ := retained_original_occupation_limit hH hcompact ha hb hell hsupport d (ε/2) hd (by linarith)
  obtain ⟨C,wH,hC,hwH,hremove⟩ := source_compact_family_removal hH hcompact
    (K:=b) (fun i r s h => hsupport i r s (Or.inr h))
  obtain ⟨BH,hBH⟩ := eventually_atTop.mp hremove
  let B₀ := max BP (max BH (max ell (2*C/ε)))
  refine ⟨B₀,max wP wH,hBP.trans_le (le_max_left _ _),hwP.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBP' : BP ≤ B := (le_max_left _ _).trans hB
  have hBH' : BH ≤ B := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hB
  have hellB : ell ≤ B :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hlarge : 2*C/ε ≤ B :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hB
  have hBpos : 0 < B := hBP.trans_le hBP'
  have hsmall : C/B ≤ ε/2 := by
    apply (div_le_iff₀ hBpos).mpr
    have hh := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have hrem := hBH B hBH' w ((le_max_right _ _).trans hw) ell hell hellB start hi h199 h23 hcons hcut
  have hret := hretained B w hBP' ((le_max_left _ _).trans hw) hcomp start hi h199 h23 hcons hcut
  have htri := abs_sub_le (uncappedFamilyValue H w ell start) (familyValue H w ell ((Real.log B)^2) start)
    (invariantAverage (arrivalTest ell H))
  linarith

theorem literal_original_prime_occupation {H : Side → ℝ×ℝ → ℝ}
    (hH : ∀ i,Continuous (H i)) (hcompact : ∀ i,HasCompactSupport (H i))
    {a b ell : ℝ} (ha : 0 < a) (hb : 0 < b) (hell : 1 ≤ ell)
    (hsupport : ∀ i : Side,∀ r s : ℝ,r < a ∨ b < r → H i (r,s)=0)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |(start.gap^2/FinitePathGeometry.weight start.side start.ratio)*
          (∑ ps ∈ ActualPrimeHigh.uncappedPrefixes w ell start,
            ErdosPrimeInputs.PrimePrefixMass.prefixWeight ps*
              H (terminal w start ps).side ((terminal w start ps).gap,(terminal w start ps).ratio))-
          invariantAverage (arrivalTest ell H)| ≤ ε := by
  simpa only [uncappedFamilyValue,nodeReward] using
    original_prime_continuous_occupation_limit hH hcompact ha hb hell hsupport d ε hd hε

end NumberTheoryLean.OriginalPrimeOccupationLimit

end

section

namespace NumberTheoryLean.PrimeOccupationDensity

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures InvariantInverseWeights OccupationBoundaries
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

noncomputable def baseMeasure : Measure (ℝ×State) := (volume : Measure ℝ).prod stateMeasure

noncomputable def density (ell : ℝ) (x : ℝ×State) : ℝ :=
  if stateRatio x.2 < Real.exp x.1/ell then (Real.exp x.1)^2/(stateWeight x.2*costMass) else 0

theorem density_nonneg (ell : ℝ) (x : ℝ×State) : 0 ≤ density ell x := by
  unfold density
  split_ifs
  · exact div_nonneg (sq_nonneg _) (mul_pos (stateWeight_pos _) costMass_pos).le
  · exact le_rfl

theorem density_measurable (ell : ℝ) : Measurable (density ell) := by
  have he := Real.measurable_exp.comp (measurable_fst : Measurable (Prod.fst : ℝ×State → ℝ))
  have hs := stateRatio_measurable.comp (measurable_snd : Measurable (Prod.snd : ℝ×State → State))
  exact Measurable.ite (measurableSet_lt hs (he.div_const ell))
    ((he.pow_const 2).div ((stateWeight_measurable.comp measurable_snd).mul_const costMass)) measurable_const

noncomputable def limitingMeasure (ell : ℝ) : Measure (ℝ×State) :=
  baseMeasure.withDensity (fun x => ENNReal.ofReal (density ell x))

theorem limiting_absolutelyContinuous (ell : ℝ) : limitingMeasure ell ≪ baseMeasure :=
  withDensity_absolutelyContinuous _ _

theorem invariant_ratio_null {B : Set ℝ} (hB : MeasurableSet B) (hnull : volume B=0) :
    stateMeasure (stateRatio ⁻¹' B)=0 := by
  rw [← state_invariance,Measure.bind_apply (stateRatio_measurable hB) stateKernel.aemeasurable]
  simp_rw [stateKernel_ratio_null _ hB hnull]
  exact lintegral_zero

theorem invariant_ratio_level_null (t : ℝ) : stateMeasure {s | stateRatio s=t}=0 := by
  exact invariant_ratio_null (measurableSet_singleton t) (measure_singleton t)

theorem exponential_level_null (r : ℝ) : (volume : Measure ℝ) {u | Real.exp u=r}=0 := by
  have hs : ({u : ℝ | Real.exp u=r}:Set ℝ).Subsingleton := by
    intro u hu v hv
    exact Real.exp_injective (hu.trans hv.symm)
  exact hs.countable.measure_zero volume

theorem gap_boundary_null (ell r : ℝ) : limitingMeasure ell {x | Real.exp x.1=r}=0 := by
  apply limiting_absolutelyContinuous ell
  have he : {x : ℝ×State | Real.exp x.1=r} = {u : ℝ | Real.exp u=r} ×ˢ (univ : Set State) := by
    ext x
    simp
  rw [baseMeasure,he,Measure.prod_prod,exponential_level_null,zero_mul]

theorem ratio_boundary_null (ell t : ℝ) : limitingMeasure ell {x | stateRatio x.2=t}=0 := by
  apply limiting_absolutelyContinuous ell
  have he : {x : ℝ×State | stateRatio x.2=t} = (univ : Set ℝ) ×ˢ {s : State | stateRatio s=t} := by
    ext x
    simp
  rw [baseMeasure,he,Measure.prod_prod,invariant_ratio_level_null,mul_zero]

noncomputable def rectangleBoundary (a b c d : ℝ) : Set (ℝ×State) :=
  {x | Real.exp x.1=a} ∪ {x | Real.exp x.1=b} ∪ {x | stateRatio x.2=c} ∪ {x | stateRatio x.2=d}

theorem rectangle_boundary_null (ell a b c d : ℝ) : limitingMeasure ell (rectangleBoundary a b c d)=0 := by
  unfold rectangleBoundary
  exact measure_union_null (measure_union_null (measure_union_null (gap_boundary_null ell a)
    (gap_boundary_null ell b)) (ratio_boundary_null ell c)) (ratio_boundary_null ell d)

end NumberTheoryLean.PrimeOccupationDensity

end

end Erdos970

end OAI
