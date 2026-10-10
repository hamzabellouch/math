import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorExpectation
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorCheck
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorCharge

namespace OAI

/-! # Expected occurrence charges under the actual independent family law -/

noncomputable section

namespace LowSpaceSubsetSum.SeparatorExpectation

open RepresentationMoments SeparatorIncidenceTable SeparatorBlocks
open scoped BigOperators

variable {g : ℕ}

theorem table_full_count {α β : Type*} (family : Array β)
    (compatible : α → β → Bool) (x : α) :
    count (table family compatible x) 0 family.size = (table family compatible x).size := by
  unfold count
  rw [List.filter_eq_self.mpr]
  · simp
  · intro j hj
    obtain ⟨hj, _⟩ := (table_mem family compatible x j).mp hj
    exact decide_eq_true ⟨Nat.zero_le _, hj⟩

abbrev IndependentFamilies (g : ℕ) (e ν : Fin 4 → ℕ) :=
  ∀ i : Fin 4, Fin (ν i) → SeparatorSample (Finset.univ : Finset (Fin g)) (e i)

def familyArrays {e ν : Fin 4 → ℕ} (draws : IndependentFamilies g e ν) :
    Fin 4 → Array (Finset (Fin g)) :=
  fun i => Array.ofFn (fun j => (draws i j).val)

theorem left_multiplicity {e ν : Fin 4 → ℕ} (draws : IndependentFamilies g e ν)
    (x : SeparatorCheck.Record g) :
    multiplicityLeft (SeparatorCheck.blocks (familyArrays draws)) x =
      ∏ i : Fin 4, (1 + incidence (fun S => SeparatorCheck.localMask i x.mask ⊆ S.val) (draws i)) := by
  simp only [multiplicityLeft, SeparatorCheck.blocks, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  change count (ofFamily (familyArrays draws i) _ _ |>.left x) 0 (familyArrays draws i).size = _
  simp only [ofFamily, SeparatorStoredMasks.containsList_eq]
  rw [table_full_count]
  have he := table_size_eq (fun j => (draws i j).val) (fun L S => decide (L ⊆ S))
    (SeparatorCheck.localMask i x.mask)
  simpa only [familyArrays, incidence, decide_eq_true_eq] using he

theorem right_multiplicity {e ν : Fin 4 → ℕ} (draws : IndependentFamilies g e ν)
    (y : SeparatorCheck.Record g) :
    multiplicityRight (SeparatorCheck.blocks (familyArrays draws)) y =
      ∏ i : Fin 4, (1 + incidence (fun S => Disjoint S.val (SeparatorCheck.localMask i y.mask))
        (draws i)) := by
  simp only [multiplicityRight, SeparatorCheck.blocks, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  change count (ofFamily (familyArrays draws i) _ _ |>.right y) 0 (familyArrays draws i).size = _
  simp only [ofFamily, SeparatorStoredMasks.avoidsList_eq]
  rw [table_full_count]
  have he := table_size_eq (fun j => (draws i j).val) (fun R S => decide (Disjoint R S))
    (SeparatorCheck.localMask i y.mask)
  have hp (j) : Disjoint (SeparatorCheck.localMask i y.mask) (draws i j).val ↔
      Disjoint (draws i j).val (SeparatorCheck.localMask i y.mask) := disjoint_comm
  simpa only [familyArrays, incidence, decide_eq_true_eq, hp] using he

theorem mean_left_multiplicity (e ν : Fin 4 → ℕ) (heg : ∀ i, e i ≤ g)
    (x : SeparatorCheck.Record g) (hce : ∀ i, (SeparatorCheck.localMask i x.mask).card ≤ e i) :
    mean (fun draws : IndependentFamilies g e ν =>
      (multiplicityLeft (SeparatorCheck.blocks (familyArrays draws)) x : ℝ)) =
      ∏ i : Fin 4, (1 + (ν i : ℝ) *
        ((Nat.choose (g - (SeparatorCheck.localMask i x.mask).card)
            (e i - (SeparatorCheck.localMask i x.mask).card) : ℝ) / Nat.choose g (e i))) := by
  classical
  let (i : Fin 4) : Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa using heg i)).to_subtype
  simp_rw [left_multiplicity, Nat.cast_prod, Nat.cast_add, Nat.cast_one]
  rw [mean_pi_product (fun (i : Fin 4)
    (family : Fin (ν i) → SeparatorSample (Finset.univ : Finset (Fin g)) (e i)) =>
      (1 : ℝ) + incidence (fun S => SeparatorCheck.localMask i x.mask ⊆ S.val) family)]
  apply Finset.prod_congr rfl
  intro i _
  rw [mean_add, mean_const, mean_containment]
  · simp
  · exact Finset.subset_univ _
  · exact hce i
  · simpa using heg i

theorem mean_right_multiplicity (e ν : Fin 4 → ℕ) (heg : ∀ i, e i ≤ g)
    (y : SeparatorCheck.Record g) :
    mean (fun draws : IndependentFamilies g e ν =>
      (multiplicityRight (SeparatorCheck.blocks (familyArrays draws)) y : ℝ)) =
      ∏ i : Fin 4, (1 + (ν i : ℝ) *
        ((Nat.choose (g - (SeparatorCheck.localMask i y.mask).card) (e i) : ℝ) / Nat.choose g (e i))) := by
  classical
  let (i : Fin 4) : Nonempty (SeparatorSample (Finset.univ : Finset (Fin g)) (e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa using heg i)).to_subtype
  simp_rw [right_multiplicity, Nat.cast_prod, Nat.cast_add, Nat.cast_one]
  rw [mean_pi_product (fun (i : Fin 4)
    (family : Fin (ν i) → SeparatorSample (Finset.univ : Finset (Fin g)) (e i)) =>
      (1 : ℝ) + incidence (fun S => Disjoint S.val (SeparatorCheck.localMask i y.mask)) family)]
  apply Finset.prod_congr rfl
  intro i _
  rw [mean_add, mean_const, mean_avoidance]
  · simp
  · exact Finset.subset_univ _
  · simpa using heg i

theorem mean_mono {Ω : Type*} [Fintype Ω] {f h : Ω → ℝ}
    (hf : ∀ x, f x ≤ h x) : mean f ≤ mean h := by
  unfold mean
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hf x))
  positivity

theorem mean_mul_left {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  simp only [mean, ← Finset.mul_sum, mul_div_assoc]

theorem mean_list_sum {Ω α : Type*} [Fintype Ω] (xs : List α) (f : α → Ω → ℝ) :
    mean (fun x => (xs.map (fun a => f a x)).sum) = (xs.map (fun a => mean (f a))).sum := by
  induction xs with
  | nil => simp [mean]
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, mean_add, ih]

theorem coefficient_families (n : ℕ) {e ν : Fin 4 → ℕ}
    (draws : IndependentFamilies g e ν) :
    coefficient n (SeparatorCheck.blocks (familyArrays draws)) =
      6 * n + 8 + 2 * ∑ i : Fin 4, Nat.clog 2 (ν i) := by
  simp only [coefficient, SeparatorCheck.blocks, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    depth, ofFamily, familyArrays, Array.size_ofFn]

/-- Exact finite expected charges bound the actual traversal, with every input
occurrence counted separately even when its key is duplicated. -/
theorem mean_scans_le (n : ℕ) (e ν : Fin 4 → ℕ) (heg : ∀ i, e i ≤ g)
    (target : ℤ) (xs ys : List (SeparatorCheck.Record g))
    (hce : ∀ x ∈ xs, ∀ i, (SeparatorCheck.localMask i x.mask).card ≤ e i) :
    mean (fun draws : IndependentFamilies g e ν =>
      ((SeparatorCheck.run n (familyArrays draws) target xs ys).scans : ℝ)) ≤
      ((6 * n + 8 + 2 * ∑ i : Fin 4, Nat.clog 2 (ν i) : ℕ) : ℝ) *
        ((xs.map (fun x => ∏ i : Fin 4, (1 + (ν i : ℝ) *
          ((Nat.choose (g - (SeparatorCheck.localMask i x.mask).card)
            (e i - (SeparatorCheck.localMask i x.mask).card) : ℝ) / Nat.choose g (e i))))).sum +
         (ys.map (fun y => ∏ i : Fin 4, (1 + (ν i : ℝ) *
          ((Nat.choose (g - (SeparatorCheck.localMask i y.mask).card) (e i) : ℝ) /
            Nat.choose g (e i))))).sum) := by
  classical
  have hpoint (draws : IndependentFamilies g e ν) :
      ((SeparatorCheck.run n (familyArrays draws) target xs ys).scans : ℝ) ≤
      ((6 * n + 8 + 2 * ∑ i : Fin 4, Nat.clog 2 (ν i) : ℕ) : ℝ) *
        (((xs.map (multiplicityLeft (SeparatorCheck.blocks (familyArrays draws)))).sum : ℕ) +
         ((ys.map (multiplicityRight (SeparatorCheck.blocks (familyArrays draws)))).sum : ℕ)) := by
    have h := scans_le_multiplicities n Entry.value Entry.value target
      (SeparatorCheck.blocks (familyArrays draws)) xs ys
    rw [coefficient_families n draws] at h
    exact_mod_cast h
  apply (mean_mono hpoint).trans_eq
  rw [mean_mul_left]
  congr 1
  simp only [Nat.cast_list_sum, List.map_map]
  rw [mean_add, mean_list_sum, mean_list_sum]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro x hx
    exact mean_left_multiplicity e ν heg x (hce x hx)
  · congr 1
    apply List.map_congr_left
    intro y _
    exact mean_right_multiplicity e ν heg y

end LowSpaceSubsetSum.SeparatorExpectation

end

end OAI
