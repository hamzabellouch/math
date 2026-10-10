import Mathlib

namespace OAI

section
namespace SharpLogRamsey.PoissonSupport
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

def extend (S : Finset ι) (ω : S → ℕ) (i : ι) : ℕ :=
  if h : i∈S then ω ⟨i,h⟩ else 0

omit [Fintype ι] in
lemma extend_restrict (S : Finset ι) (ω : ι → ℕ) (hω : ∀ i,i∉S → ω i=0) :
    extend S (fun i : S => ω i) = ω := by
  funext i
  by_cases hi : i∈S
  · simp [extend,hi]
  · simp [extend,hi,hω i hi]

omit [Fintype ι] in
lemma restrict_extend (S : Finset ι) (ω : S → ℕ) :
    (fun i : S => extend S ω i)=ω := by
  funext i
  simp [extend,i.2]

theorem extend_hasLaw (S : Finset ι) (rate : ι → ℝ≥0) :
    HasLaw (extend S) (Measure.pi (fun i => poissonMeasure (if i∈S then rate i else 0)))
      (Measure.pi (fun i : S => poissonMeasure (rate i))) := by
  refine ⟨(measurable_of_countable _).aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton z)]
  by_cases hz : ∀ i,i∉S → z i=0
  · have he : extend S ⁻¹' {z}={fun i : S => z i} := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      constructor
      · intro h
        calc
          ω = fun i : S => extend S ω i := (restrict_extend S ω).symm
          _ = fun i : S => z i := by rw [h]
      · rintro rfl
        exact extend_restrict S z hz
    rw [he,Measure.pi_singleton,Measure.pi_singleton]
    calc
      _ = ∏ i ∈ S, poissonMeasure (rate i) {z i} :=
        prod_coe_sort S (fun i => poissonMeasure (rate i) {z i})
      _ = ∏ i ∈ S, poissonMeasure (if i∈S then rate i else 0) {z i} := by
        apply prod_congr rfl
        intro i hi
        rw [ite_eq_left hi]
      _ = _ := prod_subset (subset_univ S) (fun i _ hi => by
        simp only [ite_eq_right hi,hz i hi,poissonMeasure_singleton]
        norm_num)
  · obtain ⟨i,hiS,hzi⟩ := not_forall.mp hz |>.imp (fun i h => by simpa using h)
    have he : extend S ⁻¹' {z}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh := congrFun (Set.mem_singleton_iff.mp hω) i
      exact hzi (by simpa [extend,hiS] using hh.symm)
    rw [he,measure_empty,Measure.pi_singleton]
    symm
    apply prod_eq_zero (mem_univ i)
    simp only [ite_eq_right hiS,poissonMeasure_singleton]
    have hn : z i≠0 := hzi
    simp [hn]

lemma sum_extend (S : Finset ι) (ω : S → ℕ) :
    (∑ i,extend S ω i)=∑ i : S,ω i := by
  classical
  rw [←sum_subset (subset_univ S) (fun i _ hi => by simp [extend,hi])]
  rw [←sum_coe_sort]
  apply sum_congr rfl
  intro i _
  simp [extend,i.2]

end
end SharpLogRamsey.PoissonSupport

end

end OAI
