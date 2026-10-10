import OAI.Combinatorics.BalancedRyser.Local.LocalFiberBounds
import OAI.Combinatorics.BalancedRyser.Local.LocalPrescribedGeometry

namespace OAI

namespace Balanced.Local.PrescribedGeometry

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {P : EqualityPattern b κ}
variable {a : DirectionAssignment F b κ} {bits : Bits b}
variable {p : Point F} {M N : MergedPairs F}

def unusedDirections (a : DirectionAssignment F b κ) : Finset (Direction F) :=
  Finset.univ \ Finset.univ.image a.2

omit [Field F] in
@[simp] theorem mem_unusedDirections (d : Direction F) :
    d ∈ unusedDirections a ↔ d ∉ Finset.univ.image a.2 := by
  simp [unusedDirections]

theorem indexedThrough_congr (U : Finset (Direction F)) (z : Point F)
    (hMN : ∀ d ∈ U, M d = N d) : indexedThrough M U z = indexedThrough N U z := by
  ext ds
  simp only [indexedThrough, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨hd, hz⟩ <;> refine ⟨hd, ?_⟩
  · simpa only [constituent, hMN ds.1 hd] using hz
  · simpa only [constituent, hMN ds.1 hd] using hz

theorem prescribedPartners_fixedUnused_witness (hE : Eligible P a)
    (hA : Admissible P a bits p M)
    (hMN : ∀ d ∈ unusedDirections a, M d = N d)
    (i : Fin b) {x : Point F} (hx : x ∈ prescribedPartners P a bits p M) :
    ∃ l ∈ partnerCandidates N (unusedDirections a) p,
      l ≠ lineThrough (a.1 i) p ∧ OnLine x l := by
  obtain ⟨_, ⟨d, s⟩, hd, hp, hx⟩ :=
    (mem_prescribedPartners_iff_unused hE hA x).mp hx
  have hdU : d ∈ unusedDirections a := mem_unusedDirections d |>.mpr hd
  have heq (t : Bool) : constituent M d t = constituent N d t := by
    simp only [constituent, hMN d hdU]
  refine ⟨constituent N d (!s), partner_mem_partnerCandidates N _ p d s hdU ?_, ?_, ?_⟩
  · exact heq s ▸ hp
  · intro hl
    apply hA.2.2.2.1 i
    exact Finset.mem_image.mpr ⟨(d, !s), Finset.mem_univ _, (heq (!s)).trans hl⟩
  · exact heq (!s) ▸ hx

theorem fixedUnused_multiplicity_le (hA : Admissible P a bits p M)
    (hMN : ∀ d ∈ unusedDirections a, M d = N d) (z : Point F) :
    (indexedThrough N (unusedDirections a) z).card ≤ logBudget F := by
  rw [← indexedThrough_congr (unusedDirections a) z hMN]
  exact indexedThrough_card_le M _ z _ (hA.2.2.2.2 z)

theorem admissible_precoverage_fiber_probability_le (hE : Eligible P a)
    (N : MergedPairs F) (Ms : F → MergedPairs F) (ij : Fin b × Fin 4)
    (hfixed : ∀ t d, d ∈ unusedDirections a → Ms t d = N d)
    (hinj : Function.Injective (fun t => prescribedPoint P a bits (Ms t) ij))
    (hon : ∀ t, OnLine (prescribedPoint P a bits (Ms t) ij)
      (lineThrough (a.1 ij.1) p)) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | Admissible P a bits p (Ms t) ∧
        prescribedPoint P a bits (Ms t) ij ∈ prescribedPartners P a bits p (Ms t)}).toReal ≤
      (logBudget F : ℝ) / Fintype.card F := by
  by_cases hB : (indexedThrough N (unusedDirections a) p).card ≤ logBudget F
  · apply (uniform_probability_mono _ _ ?_).trans
      (nonTarget_line_union_probability_le (lineThrough (a.1 ij.1) p)
        (partnerCandidates N (unusedDirections a) p)
        (fun t => prescribedPoint P a bits (Ms t) ij) hinj hon |>.trans ?_)
    · rintro t ⟨hA, ht⟩
      exact prescribedPartners_fixedUnused_witness hE hA (hfixed t) ij.1 ht
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_partnerCandidates_le N _ p _ hB
  · have hempty : {t | Admissible P a bits p (Ms t) ∧
        prescribedPoint P a bits (Ms t) ij ∈ prescribedPartners P a bits p (Ms t)} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hA _
      exact hB (fixedUnused_multiplicity_le hA (hfixed t) p)
    rw [hempty]
    simpa using (div_nonneg (Nat.cast_nonneg (logBudget F))
      (Nat.cast_nonneg (Fintype.card F)) : (0 : ℝ) ≤
        (logBudget F : ℝ) / Fintype.card F)

theorem unusedMerged_fixedUnused_witness
    (hA : Admissible P a bits p M)
    (hMN : ∀ d ∈ unusedDirections a, M d = N d)
    (i : Fin b) (z x : Point F)
    (hpair : ∃ d ∈ unusedDirections a,
      z ∈ mergedPoints M d ∧ x ∈ mergedPoints M d) :
    ∃ l ∈ mergedCandidates N (unusedDirections a) z,
      l ≠ lineThrough (a.1 i) p ∧ OnLine x l := by
  obtain ⟨d, hd, hz, hx⟩ := hpair
  have hz' : ∃ s : Bool, OnLine z (constituent M d s) := by
    simpa [mergedPoints, linePoints, Bool.exists_bool] using hz
  have hx' : ∃ s : Bool, OnLine x (constituent M d s) := by
    simpa [mergedPoints, linePoints, Bool.exists_bool] using hx
  obtain ⟨s, hs⟩ := hz'
  obtain ⟨t, ht⟩ := hx'
  have heq (u : Bool) : constituent M d u = constituent N d u := by
    simp only [constituent, hMN d hd]
  refine ⟨constituent N d t,
    constituent_mem_mergedCandidates N _ z d s t hd (heq s ▸ hs), ?_, heq t ▸ ht⟩
  intro hl
  exact hA.2.2.2.1 i
    (Finset.mem_image.mpr ⟨(d, t), Finset.mem_univ _, (heq t).trans hl⟩)

theorem admissible_unusedMerged_fiber_probability_le
    (N : MergedPairs F) (Ms : F → MergedPairs F) (ij : Fin b × Fin 4) (z : Point F)
    (hfixed : ∀ t d, d ∈ unusedDirections a → Ms t d = N d)
    (hinj : Function.Injective (fun t => prescribedPoint P a bits (Ms t) ij))
    (hon : ∀ t, OnLine (prescribedPoint P a bits (Ms t) ij)
      (lineThrough (a.1 ij.1) p)) :
    ((PMF.uniformOfFintype F).toOuterMeasure
      {t | Admissible P a bits p (Ms t) ∧
        ∃ d ∈ unusedDirections a, z ∈ mergedPoints (Ms t) d ∧
          prescribedPoint P a bits (Ms t) ij ∈ mergedPoints (Ms t) d}).toReal ≤
      (2 * (logBudget F : ℝ)) / Fintype.card F := by
  by_cases hB : (indexedThrough N (unusedDirections a) z).card ≤ logBudget F
  · apply (uniform_probability_mono _ _ ?_).trans
      (nonTarget_line_union_probability_le (lineThrough (a.1 ij.1) p)
        (mergedCandidates N (unusedDirections a) z)
        (fun t => prescribedPoint P a bits (Ms t) ij) hinj hon |>.trans ?_)
    · rintro t ⟨hA, ht⟩
      exact unusedMerged_fixedUnused_witness hA (hfixed t) ij.1 z _ ht
    · apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_mergedCandidates_le N _ z _ hB
  · have hempty : {t | Admissible P a bits p (Ms t) ∧
        ∃ d ∈ unusedDirections a, z ∈ mergedPoints (Ms t) d ∧
          prescribedPoint P a bits (Ms t) ij ∈ mergedPoints (Ms t) d} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hA _
      exact hB (fixedUnused_multiplicity_le hA (hfixed t) z)
    rw [hempty]
    simpa using (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg (logBudget F)))
      (Nat.cast_nonneg (Fintype.card F)) : (0 : ℝ) ≤
        (2 * (logBudget F : ℝ)) / Fintype.card F)

end
end Balanced.Local.PrescribedGeometry

end OAI
