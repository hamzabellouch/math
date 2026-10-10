import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationBlockCardinality

namespace OAI

namespace Balanced.SelectionOccupancy

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

def secondConstituents : Finset (Line F) :=
  Finset.univ.image (fun d => constituent C.merged d true)

def initial (l : Line F) : Finset (Point F) :=
  if l ∈ secondConstituents C then linePoints l
  else (linePoints l).filter (fun p => ∀ d, ¬ OnLine p (constituent C.merged d true))

def final (l : Line F) : Finset (Point F) :=
  (initial C l).filter (fun p => ∀ S ∈ C.splitLines, S ≠ l → ¬ OnLine p S)

lemma initial_subset_line (l : Line F) : initial C l ⊆ linePoints l := by
  unfold initial
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

lemma final_subset_initial (l : Line F) : final C l ⊆ initial C l :=
  Finset.filter_subset _ _

theorem initial_card_lower_bound (c₀ : ℝ) (hc₀ : c₀ ≤ 1)
    (hbase : ∀ l, l ∉ secondConstituents C →
      c₀ * Fintype.card F ≤
        (((linePoints l).filter (fun p => ∀ d,
          ¬ OnLine p (constituent C.merged d true))).card : ℝ)) :
    ∀ l, c₀ * Fintype.card F ≤ ((initial C l).card : ℝ) := by
  intro l
  by_cases hl : l ∈ secondConstituents C
  · rw [initial, ite_eq_left hl, linePoints_card]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) hc₀
  · simpa [initial, hl] using hbase l hl

omit [Field F] in
lemma mem_secondConstituents_iff (l : Line F) :
    l ∈ secondConstituents C ↔ ∃ d, constituent C.merged d true = l := by
  simp [secondConstituents]

omit [Field F] in
lemma secondConstituent_mem (d : Direction F) :
    constituent C.merged d true ∈ secondConstituents C := by
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩

lemma final_eq_initial_inter_retained (l : Line F) (hl : l ∉ C.splitLines) :
    final C l = initial C l ∩ C.retained := by
  ext p
  simp only [final, Finset.mem_filter, Finset.mem_inter, Configuration.retained,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, havoid⟩
    refine ⟨hp, ?_⟩
    intro S hS
    exact havoid S hS (fun heq => hl (heq ▸ hS))
  · rintro ⟨hp, havoid⟩
    exact ⟨hp, fun S hS _ => havoid S hS⟩

lemma mem_core_iff (p : Point F) :
    p ∈ C.core ↔ p ∈ C.retained ∧
      ∀ d, ¬ OnLine p (constituent C.merged d true) := by
  simp only [Configuration.core, Configuration.retained, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨fun S hS => h S (Finset.mem_union_left _ hS), ?_⟩
    intro d
    exact h _ (Finset.mem_union_right _ (secondConstituent_mem C d))
  · rintro ⟨hs, hm⟩ l hl
    rcases Finset.mem_union.mp hl with hsplit | hsecond
    · exact hs l hsplit
    · rcases Finset.mem_image.mp hsecond with ⟨d, _, rfl⟩
      exact hm d

theorem final_eq_core_inter (l : Line F) (hl : l ∉ C.deletedLines) :
    final C l = linePoints l ∩ C.core := by
  have hs : l ∉ C.splitLines := fun h => hl (Finset.mem_union_left _ h)
  have hm : l ∉ secondConstituents C := fun h => hl (Finset.mem_union_right _ h)
  rw [final_eq_initial_inter_retained C l hs, initial, ite_eq_right hm]
  ext p
  simp only [Finset.mem_inter, Finset.mem_filter, mem_core_iff C]
  tauto

theorem final_secondConstituent (hV : C.Valid) (d : Direction F) :
    final C (constituent C.merged d true) =
      linePoints (constituent C.merged d true) ∩ C.retained := by
  have hs : constituent C.merged d true ∉ C.splitLines := by
    intro h
    exact Finset.disjoint_left.mp (C.split_disjoint_constituent hV) h
      (C.constituent_mem_lines d true)
  rw [final_eq_initial_inter_retained C _ hs, initial,
    ite_eq_left (secondConstituent_mem C d)]

theorem occupancy_of_final (hV : C.Valid) (ρ : ℝ) (B : ℕ)
    (hmultiplicity : ∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤ B)
    (hfinal : ∀ l, ρ * Fintype.card F ≤ ((final C l).card : ℝ)) :
    C.Occupancy ρ B := by
  refine ⟨hmultiplicity, ?_, ?_⟩
  · intro l hl
    simpa [final_eq_core_inter C l hl] using hfinal l
  · intro d
    simpa [final_secondConstituent C hV d] using hfinal (constituent C.merged d true)

omit [Field F] in
lemma initialDeletedLines_eq : initialDeletedLines C.merged = secondConstituents C := rfl

lemma initiallyRetained_inter_line (l : Line F) :
    linePoints l ∩ initiallyRetained C.merged =
      (linePoints l).filter (fun p => ∀ d, ¬ OnLine p (constituent C.merged d true)) := by
  ext p
  simp [initiallyRetained, initialDeletedLines, Finset.mem_filter]

lemma constituent_multiplicity_le_sampled (p : Point F) :
    ((constituentLines C.merged).filter (OnLine p)).card ≤ sampledMultiplicity C.merged p := by
  have heq : (constituentLines C.merged).filter (OnLine p) =
      (Finset.univ.filter (fun ds : Direction F × Bool =>
        OnLine p (constituent C.merged ds.1 ds.2))).image
          (fun ds => constituent C.merged ds.1 ds.2) := by
    simp only [constituentLines, Finset.filter_image]
  rw [heq]
  exact Finset.card_image_le

theorem candidate_good_initial {c Cbound : ℝ}
    (hgood : CandidateGraphGood C.merged c Cbound) :
    (∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤
      ⌈Real.log (Fintype.card F : ℝ)⌉₊) ∧
    ∀ l, (1 / 5 : ℝ) * Fintype.card F ≤ ((initial C l).card : ℝ) := by
  refine ⟨?_, initial_card_lower_bound C (1 / 5) (by norm_num) ?_⟩
  · intro p
    exact (constituent_multiplicity_le_sampled C p).trans (hgood.2.2.2.1 p)
  · intro l hl
    have h := hgood.2.2.2.2 l hl
    simpa only [initiallyRetained_inter_line C l] using h

theorem occupancy_of_candidate_good_final {c Cbound ρ : ℝ}
    (hV : C.Valid) (hgood : CandidateGraphGood C.merged c Cbound)
    (hfinal : ∀ l, ρ * Fintype.card F ≤ ((final C l).card : ℝ)) :
    C.Occupancy ρ ⌈Real.log (Fintype.card F : ℝ)⌉₊ :=
  occupancy_of_final C hV ρ _ (candidate_good_initial C hgood).1 hfinal

end
end Balanced.SelectionOccupancy

end OAI
