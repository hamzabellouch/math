import OAI.NumberTheory.TwoPointCorrelations.MRTMultiscaleEnergy

namespace OAI

/-! The first-small-band frequency partition. Every later class supplies
an actual large polynomial in the preceding band; the exceptional set is
exactly the set on which every band has a large polynomial. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtSmallFrequencyBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (j : ℕ) : Set ℝ :=
  {t | ∀ k ∈ K j, ‖Q j k t‖ ≤ A j k}

noncomputable def mrtFirstSmallBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (j : ℕ) : Set ℝ :=
  mrtSmallFrequencyBand K Q A j \ ⋃ i ∈ range j, mrtSmallFrequencyBand K Q A i

noncomputable def mrtNoSmallBand {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (J : ℕ) : Set ℝ :=
  (⋃ j ∈ range J, mrtSmallFrequencyBand K Q A j)ᶜ

lemma mrt_small_frequency_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtSmallFrequencyBand K Q A j) := by
  have he : mrtSmallFrequencyBand K Q A j =
      ⋂ k ∈ K j, {t | ‖Q j k t‖ ≤ A j k} := by
    ext t
    simp [mrtSmallFrequencyBand]
  rw [he]
  exact (K j).measurableSet_biInter (fun k _ =>
    (isClosed_le (hQ j k).norm continuous_const).measurableSet)

lemma mrt_first_small_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (j : ℕ) :
    MeasurableSet (mrtFirstSmallBand K Q A j) :=
  (mrt_small_frequency_band_measurable K Q A hQ j).diff
    ((range j).measurableSet_biUnion (fun i _ =>
      mrt_small_frequency_band_measurable K Q A hQ i))

lemma mrt_no_small_band_measurable {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (J : ℕ) :
    MeasurableSet (mrtNoSmallBand K Q A J) :=
  ((range J).measurableSet_biUnion (fun j _ =>
    mrt_small_frequency_band_measurable K Q A hQ j)).compl

lemma mrt_first_small_band_disjoint {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (mrtFirstSmallBand K Q A i) (mrtFirstSmallBand K Q A j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hj.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨mem_range.mpr hlt, hi.1⟩⟩)
  · exact hi.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hgt, hj.1⟩⟩)

theorem mrt_frequency_partition {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) (J : ℕ) (S : Set ℝ) :
    S = (S ∩ mrtNoSmallBand K Q A J) ∪
      ⋃ j ∈ range J, S ∩ mrtFirstSmallBand K Q A j := by
  ext t
  constructor
  · intro ht
    by_cases he : ∃ j < J, t ∈ mrtSmallFrequencyBand K Q A j
    · right
      let j := Nat.find he
      have hj := Nat.find_spec he
      apply Set.mem_iUnion.mpr
      refine ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hj.1, ht, hj.2, ?_⟩⟩
      intro hprev
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hprev
      obtain ⟨hij, hit⟩ := Set.mem_iUnion.mp hi
      have hil : i < j := mem_range.mp hij
      exact Nat.find_min he hil ⟨hil.trans hj.1, hit⟩
    · left
      refine ⟨ht, ?_⟩
      intro hsmall
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hsmall
      obtain ⟨hjJ, hjt⟩ := Set.mem_iUnion.mp hj
      exact he ⟨j, mem_range.mp hjJ, hjt⟩
  · rintro (ht | ht)
    · exact ht.1
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
      obtain ⟨_, hjt⟩ := Set.mem_iUnion.mp hj
      exact hjt.1

theorem mrt_later_band_large_witness {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {j : ℕ} (hj : 0 < j)
    {t : ℝ} (ht : t ∈ mrtFirstSmallBand K Q A j) :
    ∃ k ∈ K (j - 1), A (j - 1) k < ‖Q (j - 1) k t‖ := by
  have hn : t ∉ mrtSmallFrequencyBand K Q A (j - 1) := by
    intro hsmall
    exact ht.2 (Set.mem_iUnion.mpr ⟨j - 1,
      Set.mem_iUnion.mpr ⟨mem_range.mpr (by omega), hsmall⟩⟩)
  simp only [mrtSmallFrequencyBand, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hn
  exact hn

theorem mrt_no_small_band_large_witness {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ) {J j : ℕ} (hj : j < J)
    {t : ℝ} (ht : t ∈ mrtNoSmallBand K Q A J) :
    ∃ k ∈ K j, A j k < ‖Q j k t‖ := by
  have hn : t ∉ mrtSmallFrequencyBand K Q A j := by
    intro hsmall
    exact ht (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨mem_range.mpr hj, hsmall⟩⟩)
  simp only [mrtSmallFrequencyBand, Set.mem_ofPred_eq, not_forall, not_le, exists_prop] at hn
  exact hn

theorem mrt_frequency_partition_integral {κ : Type*} (K : ℕ → Finset κ)
    (Q : ℕ → κ → ℝ → ℂ) (A : ℕ → κ → ℝ)
    (hQ : ∀ j k, Continuous (Q j k)) (J : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (f : ℝ → ℝ) (hf : IntegrableOn f S) :
    (∫ t in S, f t) = (∫ t in S ∩ mrtNoSmallBand K Q A J, f t) +
      ∑ j ∈ range J, ∫ t in S ∩ mrtFirstSmallBand K Q A j, f t := by
  let E := S ∩ mrtNoSmallBand K Q A J
  let B := fun j => S ∩ mrtFirstSmallBand K Q A j
  have hBsub (j : ℕ) : B j ⊆ S := Set.inter_subset_left
  have hBmeas (j : ℕ) : MeasurableSet (B j) :=
    hS.inter (mrt_first_small_band_measurable K Q A hQ j)
  have hBdis : Set.Pairwise (↑(range J)) (fun i j => Disjoint (B i) (B j)) := by
    intro i _ j _ hij
    exact (mrt_first_small_band_disjoint K Q A hij).mono
      Set.inter_subset_right Set.inter_subset_right
  have hsum := integral_biUnion_finset (range J) (fun j _ => hBmeas j) hBdis
    (fun j _ => hf.mono_set (hBsub j))
  have hdis : Disjoint E (⋃ j ∈ range J, B j) := by
    apply Set.disjoint_left.mpr
    intro t ht hU
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hU
    obtain ⟨hjJ, hjt⟩ := Set.mem_iUnion.mp hj
    exact ht.2 (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjJ, hjt.2.1⟩⟩)
  have hUsub : (⋃ j ∈ range J, B j) ⊆ S := by
    intro t ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
    obtain ⟨_, hjt⟩ := Set.mem_iUnion.mp hj
    exact hjt.1
  conv_lhs => rw [mrt_frequency_partition K Q A J S]
  rw [setIntegral_union hdis ((range J).measurableSet_biUnion (fun j _ => hBmeas j))
    (hf.mono_set Set.inter_subset_left) (hf.mono_set hUsub), hsum]

end TwoPointCorrelations

end OAI
