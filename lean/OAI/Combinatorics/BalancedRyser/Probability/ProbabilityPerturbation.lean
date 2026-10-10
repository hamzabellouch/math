import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

namespace Balanced

open MeasureTheory Filter
open scoped Topology

section SingleSpace

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem probReal_inter_ge_sub (A G : Set Ω) (hG : MeasurableSet G) :
    μ.real A - (1 - μ.real G) ≤ μ.real (A ∩ G) := by
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := A) hG
  have hbound : μ.real (A \ G) ≤ 1 - μ.real G := by
    rw [← probReal_compl_eq_one_sub (μ := μ) hG]
    exact measureReal_mono (Set.sdiff_subset_compl A G)
  linarith

theorem abs_probReal_inter_sub_le (A G : Set Ω) (hG : MeasurableSet G) :
    |μ.real (A ∩ G) - μ.real A| ≤ 1 - μ.real G := by
  have hmono : μ.real (A ∩ G) ≤ μ.real A :=
    measureReal_mono Set.inter_subset_left
  rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
  have := probReal_inter_ge_sub μ A G hG
  linarith

end SingleSpace

section VaryingSpaces

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem tendsto_probReal_inter_of_good
    {l : Filter ι} (A G : ∀ i, Set (Ω i)) (hGmeas : ∀ i, MeasurableSet (G i))
    {L : ℝ} (hA : Tendsto (fun i => (μ i).real (A i)) l (𝓝 L))
    (hG : Tendsto (fun i => (μ i).real (G i)) l (𝓝 1)) :
    Tendsto (fun i => (μ i).real (A i ∩ G i)) l (𝓝 L) := by
  have hlower : Tendsto (fun i => (μ i).real (A i) - (1 - (μ i).real (G i)))
      l (𝓝 L) := by
    simpa using hA.sub ((tendsto_const_nhds (x := (1 : ℝ))).sub hG)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hA
    (fun i => probReal_inter_ge_sub (μ i) (A i) (G i) (hGmeas i))
    (fun i => measureReal_mono Set.inter_subset_left)

end VaryingSpaces

theorem pmf_outerReal_mono {Ω : Type*} (p : PMF Ω) {A B : Set Ω} (h : A ⊆ B) :
    (p.toOuterMeasure A).toReal ≤ (p.toOuterMeasure B).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hB : MeasurableSet B := by trivial
  have hmono := measureReal_mono (μ := p.toMeasure) h
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hB] using hmono

theorem pmf_outerReal_compl {Ω : Type*} (p : PMF Ω) (A : Set Ω) :
    (p.toOuterMeasure Aᶜ).toReal = 1 - (p.toOuterMeasure A).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hcompl := probReal_compl_eq_one_sub (μ := p.toMeasure) hA
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA.compl] using hcompl

theorem tendsto_pmf_outerReal_inter_of_good
    {ι : Type*} {Ω : ι → Type*} (p : ∀ i, PMF (Ω i))
    {l : Filter ι} (A G : ∀ i, Set (Ω i)) {L : ℝ}
    (hA : Tendsto (fun i => ((p i).toOuterMeasure (A i)).toReal) l (𝓝 L))
    (hG : Tendsto (fun i => ((p i).toOuterMeasure (G i)).toReal) l (𝓝 1)) :
    Tendsto (fun i => ((p i).toOuterMeasure (A i ∩ G i)).toReal) l (𝓝 L) := by
  let : ∀ i, MeasurableSpace (Ω i) := fun _ => ⊤
  have heq : ∀ i (E : Set (Ω i)), (p i).toMeasure.real E =
      ((p i).toOuterMeasure E).toReal := by
    intro i E
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_apply_eq_toOuterMeasure_apply (p i) (by trivial))
  have hA' : Tendsto (fun i => (p i).toMeasure.real (A i)) l (𝓝 L) := by
    simpa only [heq] using hA
  have hG' : Tendsto (fun i => (p i).toMeasure.real (G i)) l (𝓝 1) := by
    simpa only [heq] using hG
  simpa only [heq] using tendsto_probReal_inter_of_good
    (fun i => (p i).toMeasure) A G (fun _ => by trivial) hA' hG'

end Balanced

end OAI
