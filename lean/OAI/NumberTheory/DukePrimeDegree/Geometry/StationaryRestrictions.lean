import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Order.PartialSups
import Mathlib.Algebra.Order.SuccPred.PartialSups
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Logic.Encodable.Lattice

namespace OAI

/-! # Gluing stationary restrictions over a countable cover

For a Markov kernel, stationary restrictions of one finite measure are
closed under intersections and unions. Thus local stationarity on a
countable almost-everywhere cover implies global stationarity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree

variable {Y : Type*} [MeasurableSpace Y]

private lemma bind_kernel_mono (κ : Kernel Y Y) {μ ν : Measure Y} (h : μ ≤ ν) :
    μ.bind κ ≤ ν.bind κ := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA κ.measurable.aemeasurable,
    Measure.bind_apply hA κ.measurable.aemeasurable]
  exact lintegral_mono' h le_rfl

private lemma bind_kernel_add (κ : Kernel Y Y) (μ ν : Measure Y) :
    (μ+ν).bind κ = μ.bind κ + ν.bind κ := by
  ext A hA
  simp only [Measure.bind_apply hA κ.measurable.aemeasurable, Measure.add_apply,
    lintegral_add_measure]

private lemma bind_kernel_univ (κ : Kernel Y Y) [IsMarkovKernel κ] (μ : Measure Y) :
    μ.bind κ univ = μ univ := by
  rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]
  simp only [measure_univ, lintegral_const, one_mul]

theorem bind_kernel_real (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) (A : Set Y) (hA : MeasurableSet A) :
    (μ.bind κ).real A = ∫ y, (κ y).real A ∂μ := by
  rw [Measure.real, Measure.bind_apply hA κ.measurable.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hA).aemeasurable
    (Filter.Eventually.of_forall fun y => measure_lt_top (κ y) A)).symm

theorem bind_eq_of_real_integrals (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (h : ∀ A, MeasurableSet A → (∫ y, (κ y).real A ∂μ) = μ.real A) :
    μ.bind κ = μ := by
  let : IsFiniteMeasure (μ.bind κ) :=
    ⟨by rw [bind_kernel_univ]; exact measure_lt_top μ univ⟩
  ext A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.bind κ).real A = μ.real A
  rw [bind_kernel_real κ μ A hA]
  exact h A hA

theorem stationary_restrict_inter (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (E F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hsE : (μ.restrict E).bind κ = μ.restrict E)
    (hsF : (μ.restrict F).bind κ = μ.restrict F) :
    (μ.restrict (E ∩ F)).bind κ = μ.restrict (E ∩ F) := by
  let ν := (μ.restrict (E ∩ F)).bind κ
  have hνE : ν ≤ μ.restrict E := by
    simpa only [ν, hsE] using bind_kernel_mono κ
      (Measure.restrict_mono_set μ (inter_subset_left : E ∩ F ⊆ E))
  have hνF : ν ≤ μ.restrict F := by
    simpa only [ν, hsF] using bind_kernel_mono κ
      (Measure.restrict_mono_set μ (inter_subset_right : E ∩ F ⊆ F))
  have hmem : ∀ᵐ y ∂ν, y ∈ E ∩ F := by
    filter_upwards [(ae_mono hνE) (ae_restrict_mem hE),
      (ae_mono hνF) (ae_restrict_mem hF)] with y hyE hyF
    exact ⟨hyE,hyF⟩
  have hν : ν ≤ μ.restrict (E ∩ F) := by
    have H := Measure.restrict_mono_measure (hνE.trans Measure.restrict_le_self) (E ∩ F)
    rwa [Measure.restrict_eq_self_of_ae_mem hmem] at H
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le (μ.restrict (E ∩ F)) hν
  exact Measure.eq_of_le_of_measure_univ_eq hν (bind_kernel_univ κ _)

theorem stationary_restrict_union (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (E F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hsE : (μ.restrict E).bind κ = μ.restrict E)
    (hsF : (μ.restrict F).bind κ = μ.restrict F) :
    (μ.restrict (E ∪ F)).bind κ = μ.restrict (E ∪ F) := by
  have hsI := stationary_restrict_inter κ μ E F hE hF hsE hsF
  have hsum := Measure.restrict_union_add_inter (μ := μ) E hF
  have H := congrArg (fun ν : Measure Y => ν.bind κ) hsum
  rw [bind_kernel_add, bind_kernel_add, hsI, hsE, hsF] at H
  have H' : μ.restrict (E ∩ F) + (μ.restrict (E ∪ F)).bind κ =
      μ.restrict (E ∩ F) + μ.restrict (E ∪ F) := by
    simpa only [add_comm] using H.trans hsum.symm
  exact le_antisymm (Measure.le_of_add_le_add_left H'.le)
    (Measure.le_of_add_le_add_left H'.ge)

theorem stationary_restrict_iUnion_of_monotone (κ : Kernel Y Y)
    (μ : Measure Y) (E : ℕ → Set Y) (hE : ∀ n, MeasurableSet (E n)) (hm : Monotone E)
    (hs : ∀ n, (μ.restrict (E n)).bind κ = μ.restrict (E n)) :
    (μ.restrict (⋃ n, E n)).bind κ = μ.restrict (⋃ n, E n) := by
  ext A hA
  let f := fun n => (E n).indicator (fun y => κ y A)
  have hf n : Measurable (f n) := (κ.measurable_coe hA).indicator (hE n)
  have hfm : Monotone f := by
    intro i j hij y
    exact Set.indicator_le_indicator_of_subset (hm hij) (fun _ => bot_le) y
  have he : (fun y => ⨆ n, f n y) = (⋃ n, E n).indicator (fun y => κ y A) := by
    funext y
    by_cases hy : y ∈ ⋃ n, E n
    · rw [Set.indicator_of_mem hy]
      apply le_antisymm
      · exact iSup_le fun n => Set.indicator_le_self (E n) (fun y => κ y A) y
      · obtain ⟨n,hn⟩ := mem_iUnion.mp hy
        exact le_iSup_of_le n (by dsimp only [f]; rw [Set.indicator_of_mem hn])
    · have hy' n : y ∉ E n := fun hn => hy (mem_iUnion.mpr ⟨n,hn⟩)
      have hz n : f n y = 0 := by
        dsimp only [f]
        rw [Set.indicator_of_notMem (hy' n)]
      simp only [hz, iSup_const, Set.indicator_of_notMem hy]
  rw [Measure.bind_apply hA κ.measurable.aemeasurable,
    ←lintegral_indicator (MeasurableSet.iUnion hE), ←he, lintegral_iSup hf hfm]
  simp only [f, lintegral_indicator (hE _),
    ←Measure.bind_apply hA κ.measurable.aemeasurable, hs]
  exact (Measure.restrict_iUnion_apply_eq_iSup hm.directed_le hA).symm

/-- The local restrictions must use the same actual Markov kernel.
No global stationarity hypothesis is used. -/
theorem stationary_of_countable_restrictions (κ : Kernel Y Y) [IsMarkovKernel κ]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (E : ℕ → Set Y) (hE : ∀ n, MeasurableSet (E n))
    (hcover : ∀ᵐ y ∂μ, y ∈ ⋃ n, E n)
    (hs : ∀ n, (μ.restrict (E n)).bind κ = μ.restrict (E n)) :
    μ.bind κ = μ := by
  have hpartial n : MeasurableSet (partialSups E n) ∧
      (μ.restrict (partialSups E n)).bind κ = μ.restrict (partialSups E n) := by
    induction n with
    | zero => simpa only [partialSups_zero] using And.intro (hE 0) (hs 0)
    | succ n ih =>
      rw [partialSups_add_one]
      exact ⟨ih.1.union (hE (n+1)),
        stationary_restrict_union κ μ _ _ ih.1 (hE (n+1)) ih.2 (hs (n+1))⟩
  have H := stationary_restrict_iUnion_of_monotone κ μ (partialSups E)
    (fun n => (hpartial n).1) (partialSups_monotone E) (fun n => (hpartial n).2)
  have he : (⋃ n, partialSups E n) = ⋃ n, E n := iSup_partialSups_eq E
  rw [he, Measure.restrict_eq_self_of_ae_mem hcover] at H
  exact H

/-- The cover may use any countable index type, including a countable
family of quotient charts with different coordinate domains. -/
theorem stationary_of_countable_indexed_restrictions {ι : Type*} [Countable ι]
    (κ : Kernel Y Y) [IsMarkovKernel κ] (μ : Measure Y) [IsFiniteMeasure μ]
    (E : ι → Set Y) (hE : ∀ i, MeasurableSet (E i))
    (hcover : ∀ᵐ y ∂μ, y ∈ ⋃ i, E i)
    (hs : ∀ i, (μ.restrict (E i)).bind κ = μ.restrict (E i)) :
    μ.bind κ = μ := by
  let := Encodable.ofCountable ι
  let F := fun n => ⋃ i ∈ Encodable.decode₂ ι n, E i
  have hF n : MeasurableSet (F n) ∧
      (μ.restrict (F n)).bind κ = μ.restrict (F n) := by
    exact Encodable.iUnion_decode₂_cases
      (C := fun S => MeasurableSet S ∧ (μ.restrict S).bind κ = μ.restrict S)
      (by simp) (fun i => ⟨hE i,hs i⟩)
  apply stationary_of_countable_restrictions κ μ F (fun n => (hF n).1) _
    (fun n => (hF n).2)
  simpa only [F, Encodable.iUnion_decode₂] using hcover

end DukePrimeDegree

end

end OAI
