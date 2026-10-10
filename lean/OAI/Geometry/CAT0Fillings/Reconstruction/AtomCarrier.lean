import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.BorelAction
import OAI.Geometry.CAT0Fillings.Reconstruction.AtomGraphs
import OAI.Geometry.CAT0Fillings.Reconstruction.BorelAtoms

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma UnitRepresentation.borelAction {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) {f : X → ℝ}
    (hf : Measurable f) {B : ℝ≥0} (hB : ∀ z, |f z| ≤ B) (π : Fin 0 → X → ℝ) :
    currentBorelAction S f π = ∑ i, (a i : ℝ)*f (x i) := by
  classical
  let νi (i : Fin m) := ENNReal.ofReal |(a i : ℝ)| • Measure.dirac (x i)
  let : ∀ i, IsFiniteMeasure (νi i) := fun i => finite_atom_measure (a i) (x i)
  let ν : Measure X := ∑ i, νi i
  have hν : Controls S ν := h.controls hS
  have hfν : Integrable f ν := integrable_bounded_measurable ν hf hB
  have hfμ : Integrable f (currentMassMeasure hS) := integrable_bounded_measurable _ hf hB
  have hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j) := fun j => Fin.elim0 j
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation ν hfν
  have hlim := borelAction_tendsto ν hS hν hfν
    (fun n => integrable_boundedLip ν (g n).property) hg π hπ
  have he (n : ℕ) : BorelCoefficients.borelAction ν hS (g n).val π = ∑ i, (a i : ℝ)*(g n).val (x i) := by
    rw [borelAction_eq ν hS hν ⟨(g n).property,hπ⟩]
    exact h.action hS (g n).property π
  have ht : Tendsto (fun n => ∑ i, (a i : ℝ)*(g n).val (x i)) atTop
      (𝓝 (∑ i, (a i : ℝ)*f (x i))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hg
    rw [Real.dist_eq,←Finset.sum_sub_distrib]
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        Integrable (fun z => |(g n).val z-f z|) (νi i) := by
      intro i _
      exact ((integrable_boundedLip (νi i) (g n).property).sub
        (integrable_bounded_measurable (νi i) hf hB)).abs
    change _ ≤ ∫ z, |(g n).val z-f z| ∂(∑ i, νi i)
    rw [integral_finsetSum_measure hi]
    simp only [νi,integral_smul_measure,integral_dirac,
      ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul,←abs_mul,←mul_sub]
    exact Finset.abs_sum_le_sum_abs _ _
  simp only [he] at hlim
  rw [currentBorelAction_eq hS,
    borelAction_independent _ hS (currentMassMeasure_controls hS) hν hfμ hfν π hπ]
  exact tendsto_nhds_unique hlim ht

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma UnitRepresentation.atom_in_carrier {m : ℕ} {S : Functional X 0}
    (hS : IsMetricCurrent S) {a : Fin m → ℤ} {x : Fin m → X}
    (h : UnitRepresentation S a x) (ha : ∀ i, a i ≠ 0) (hx : Function.Injective x)
    {E : Set X} (_ : MeasurableSet E) (hμ : currentMassMeasure hS Eᶜ = 0) (i : Fin m) :
    x i ∈ E := by
  classical
  by_contra hi
  let f : X → ℝ := ({x i} : Set X).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator (measurableSet_singleton _)
  have hf1 (z : X) : |f z| ≤ (1 : ℝ≥0) := by
    by_cases hz : z = x i <;> simp [f,hz]
  have he : f =ᵐ[currentMassMeasure hS] 0 := by
    have hEae : ∀ᵐ z ∂currentMassMeasure hS, z ∈ E := ae_iff.mpr hμ
    filter_upwards [hEae] with z hz
    apply indicator_of_notMem
    intro hzi
    exact hi ((mem_singleton_iff.mp hzi) ▸ hz)
  have hz : currentBorelAction S f (fun j => Fin.elim0 j) = 0 := by
    rw [currentBorelAction_eq hS,borelAction_congr_ae _ hS he]
    rw [borelAction_of_integrable _ hS (integrable_zero _ _ _) _ (fun j => Fin.elim0 j)]
    simp
  rw [h.borelAction hS hf hf1] at hz
  have hs : (∑ j, (a j : ℝ)*f (x j)) = (a i : ℝ) := by
    rw [Finset.sum_eq_single i]
    · simp [f]
    · intro j _ hji
      have hne : x j ≠ x i := fun hh => hji (hx hh)
      simp [f,hne]
    · simp
  rw [hs] at hz
  exact ha i (Int.cast_eq_zero.mp hz)

end CAT0Fillings.SliceReconstruction
end

end OAI
