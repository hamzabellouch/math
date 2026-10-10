import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightSlab

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma weighted_record_suffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d)) (J : ℝ)
    (hrecord : ∀ y ∈ wordDepartures 0 w,
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 w w.length)) ℓ)
    (hJ : J < dot (realPosition (wordPath 0 w w.length)) ℓ)
    (g : Environment d → ℝ≥0∞)
    (hg : @Measurable _ _ (rowSigma {z | dot (realPosition z) ℓ ≤ J}) _ g)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    (∫⁻ ω, g ω * quenchedKernel (ω,0) ((fun X : Path d => fun j => X (w.length+j)-
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) ∂environmentLaw ν) =
      (∫⁻ ω, g ω * ENNReal.ofReal (wordWeight ω 0 w) ∂environmentLaw ν) *
        annealedLaw ν A := by
  let y := wordPath 0 w w.length
  let S : Set (Lattice d) := ↑(wordDepartures 0 w) ∪ {z | dot (realPosition z) ℓ ≤ J}
  let T : Set (Lattice d) := {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}
  let B : Set (Path d) := (fun X : Path d => fun j => X j - y) ⁻¹' A
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hBT : B ⊆ Stay T := by
    intro X hX j
    have h := hAD hX j
    change dot (realPosition y) ℓ ≤ dot (realPosition (X j)) ℓ
    change dot (realPosition 0) ℓ ≤ dot (realPosition (X j - y)) ℓ at h
    rw [dot_realPosition_sub] at h
    have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
    rw [hz] at h
    linarith
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    rcases hz with hz | hz
    · exact (not_le_of_gt (hrecord z hz)) hz'
    · exact (not_le_of_gt hJ) (hz'.trans hz)
  have hw (ω : Environment d) : quenchedKernel (ω,0)
      ((fun X : Path d => fun j => X (w.length+j)-y) ⁻¹' A ∩ wordCylinder 0 w) =
      ENNReal.ofReal (wordWeight ω 0 w) * quenchedKernel (ω,y) B := by
    have hh := quenched_prefix_future ω 0 (wordPath 0 w) (by simp) w.length hB
    change quenchedKernel (ω,0) (_ ∩ wordCylinder 0 w) =
      quenchedKernel (ω,0) (wordCylinder 0 w) * quenchedKernel (ω,y) B at hh
    rwa [quenched_wordCylinder] at hh
  change (∫⁻ ω, g ω * quenchedKernel (ω,0)
    ((fun X : Path d => fun j => X (w.length+j)-y) ⁻¹' A ∩ wordCylinder 0 w)
    ∂environmentLaw ν) = _
  simp_rw [hw, ← mul_assoc]
  have hh := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (rowSigma_le S) (rowSigma_le T) (environment_indep_rows ν hST)
    ((hg.mono (rowSigma_mono Set.subset_union_right) le_rfl).mul
      ((measurable_wordWeight_on 0 w (fun _ hz => Or.inl hz)).ennreal_ofReal))
    (measurable_quenched_stay_event_rows T y (show dot (realPosition y) ℓ ≤ dot (realPosition y) ℓ from le_rfl) B hB hBT)
  simp only [Pi.mul_apply] at hh
  rw [hh]
  rw [annealed_event_translation ν y A hA]

noncomputable def weightedAnnealed {d : ℕ} (ν : Measure (Row d))
    (g : Environment d → ℝ≥0∞) : Measure (Path d) :=
  ((environmentLaw ν).withDensity g).bind (fun ω => quenchedKernel (ω,0))

lemma weightedAnnealed_apply {d : ℕ} (ν : Measure (Row d))
    (g : Environment d → ℝ≥0∞) (hg : Measurable g)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    weightedAnnealed ν g A = ∫⁻ ω, g ω * quenchedKernel (ω,0) A ∂environmentLaw ν := by
  rw [weightedAnnealed, Measure.bind_apply hA (by fun_prop)]
  have hm : Measurable (fun ω : Environment d => quenchedKernel (ω,0) A) :=
    (Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)
  simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul
    (environmentLaw ν) hg hm

lemma weightedAnnealed_le {d : ℕ} (ν : Measure (Row d))
    (g : Environment d → ℝ≥0∞) (hg : Measurable g) (hgle : ∀ ω, g ω ≤ 1) :
    weightedAnnealed ν g ≤ annealedLaw ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [weightedAnnealed_apply ν g hg A hA, annealed_apply ν hA]
  exact lintegral_mono fun ω => mul_le_of_le_one_left' (hgle ω)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
