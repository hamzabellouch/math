import OAI.Combinatorics.BalancedRyser.Local.AlignmentNormalization
import OAI.Combinatorics.BalancedRyser.Probability.UniformConditionalProduct

namespace OAI

namespace Balanced.Local.AlignedUnused

open UniformConditionalProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def usedDirections {b κ : ℕ} (_P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) : Finset (Direction F) := Finset.univ.image a.2

abbrev UsedArray {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) := {d : Direction F // d ∈ usedDirections P a} → Bool → F

abbrev UnusedArray {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) := {d : Direction F // d ∉ usedDirections P a} → Bool → F

def split {b κ : ℕ} (P : EqualityPattern b κ) (a : DirectionAssignment F b κ) :
    MergedPairs F ≃ UsedArray P a × UnusedArray P a :=
  arraySplitEquiv (fun d => d ∈ usedDirections P a)

omit [Field F] [Fintype F] in

theorem usedDirections_eq_union {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) :
    usedDirections P a = Finset.univ.biUnion
      (fun i => generatorSet (prescribedTuple P a bits i)) := by
  simp_rw [P.generatorSet_prescribedTuple]
  rw [← Finset.biUnion_image, P.biUnion_classSet]
  rfl

omit [Fintype F] in

theorem aligned_agree {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M N : MergedPairs F) (h : ∀ d ∈ usedDirections P a, M d = N d) :
    Aligned P a bits p M ↔ Aligned P a bits p N := by
  have hp (ij : Fin b × Fin 4) :
      prescribedPoint P a bits M ij = prescribedPoint P a bits N ij := by
    apply AlignedListProbability.tuplePoint_eq_of_agree
    intro d hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    exact h _ (Finset.mem_image.mpr ⟨P.classOf ij.1 j, Finset.mem_univ _, rfl⟩)
  simp only [Aligned, hp]

def usedAligned {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (u : UsedArray P a) : Prop :=
  Aligned P a bits p ((split P a).symm (u, fun _ _ => 0))

omit [Fintype F] in
theorem aligned_iff_usedAligned {b κ : ℕ} (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    Aligned P a bits p M ↔ usedAligned P a bits p ((split P a M).1) := by
  apply aligned_agree
  intro d hd
  have heq := congrArg Prod.fst ((split P a).apply_symm_apply
    ((split P a M).1, fun _ _ => 0))
  exact (congrFun heq ⟨d, hd⟩).symm

theorem alignment_supported {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    ∃ M ∈ {M | Aligned P a bits p M},
      M ∈ (PMF.uniformOfFintype (MergedPairs F)).support := by
  have hpos := alignment_probability_pos P hκ a ha bits p
  have hex : ∃ M, Aligned P a bits p M := by
    by_contra h
    have hn : ∀ M, ¬ Aligned P a bits p M := not_exists.mp h
    have hz : offsetProbability (Aligned P a bits p) = 0 := by
      simp [offsetProbability, hn]
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨M, hM⟩ := hex
  exact ⟨M, hM, PMF.mem_support_uniformOfFintype M⟩

def alignedLaw {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    PMF (MergedPairs F) :=
  (PMF.uniformOfFintype (MergedPairs F)).filter {M | Aligned P a bits p M}
    (alignment_supported P hκ a ha bits p)

theorem usedAligned_nonempty {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    Nonempty {u : UsedArray P a // usedAligned P a bits p u} := by
  obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
  exact ⟨⟨(split P a M).1, (aligned_iff_usedAligned P a bits p M).mp hM⟩⟩

def usedLaw {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    PMF (UsedArray P a) :=
  letI := usedAligned_nonempty P hκ a ha bits p
  (PMF.uniformOfFintype {u : UsedArray P a // usedAligned P a bits p u}).map Subtype.val

theorem alignedLaw_eq_uniform_pair {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    letI := usedAligned_nonempty P hκ a ha bits p
    alignedLaw P hκ a ha bits p =
      (PMF.uniformOfFintype
        ({u : UsedArray P a // usedAligned P a bits p u} × UnusedArray P a)).map
        (fun z => (split P a).symm (z.1.1, z.2)) := by
  let := usedAligned_nonempty P hκ a ha bits p
  have hs : ∃ M ∈ {M | usedAligned P a bits p (split P a M).1},
      M ∈ (PMF.uniformOfFintype (MergedPairs F)).support := by
    obtain ⟨M, hM, hs⟩ := alignment_supported P hκ a ha bits p
    exact ⟨M, (aligned_iff_usedAligned P a bits p M).mp hM, hs⟩
  have h := uniform_filter_split (split P a) (usedAligned P a bits p) hs
  simpa only [← aligned_iff_usedAligned, alignedLaw] using h

theorem alignedLaw_eq_bind {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    alignedLaw P hκ a ha bits p =
      (usedLaw P hκ a ha bits p).bind (fun u =>
        (PMF.uniformOfFintype (UnusedArray P a)).map
          (fun v => (split P a).symm (u, v))) := by
  let := usedAligned_nonempty P hκ a ha bits p
  rw [alignedLaw_eq_uniform_pair, uniform_product_eq_bind, PMF.map_bind]
  unfold usedLaw
  rw [PMF.bind_map]
  congr 1
  funext u
  rw [PMF.map_comp]
  rfl

theorem alignedLaw_unused {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F) :
    (alignedLaw P hκ a ha bits p).map (fun M => (split P a M).2) =
      PMF.uniformOfFintype (UnusedArray P a) := by
  let := usedAligned_nonempty P hκ a ha bits p
  rw [alignedLaw_eq_uniform_pair, PMF.map_comp]
  have heq : ((fun M => (split P a M).2) ∘
      (fun z : {u : UsedArray P a // usedAligned P a bits p u} × UnusedArray P a =>
        (split P a).symm (z.1.1, z.2))) = Prod.snd := by
    funext z
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [heq]
  exact uniform_map_second

theorem alignedLaw_eq_canonical {b κ : ℕ} (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (hs : ∃ M ∈ {M | Aligned P a bits p M}, M ∈ (offsetLaw F).support) :
    alignedLaw P hκ a ha bits p = (offsetLaw F).filter {M | Aligned P a bits p M} hs := by
  simp only [alignedLaw, PartialAlignment.offsetLaw_eq_uniform]

theorem conditionedOffsetProbability_eq_alignedLaw {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (E : MergedPairs F → Prop) :
    conditionedOffsetProbability (Aligned P a bits p) E =
      ((alignedLaw P hκ a ha bits p).toOuterMeasure {M | E M}).toReal := by
  let A : MergedPairs F → Prop := Aligned P a bits p
  let : Nonempty {M : MergedPairs F // A M} := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  let : Nonempty ({M : MergedPairs F | A M} : Set (MergedPairs F)) := by
    obtain ⟨M, hM, _⟩ := alignment_supported P hκ a ha bits p
    exact ⟨⟨M, hM⟩⟩
  have hcard (H : MergedPairs F → Prop) :
      offsetProbability H = (Fintype.card {M // H M} : ℝ) / Fintype.card (MergedPairs F) := by
    unfold offsetProbability
    rw [← FiniteUniformFibers.probability_eq_sum H,
      PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
    simp [Fintype.card_subtype]
  have hnum : Fintype.card {M : {M : MergedPairs F // A M} // E M} =
      Fintype.card {M : MergedPairs F // A M ∧ E M} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter A E)
  change offsetProbability (fun M => A M ∧ E M) / offsetProbability A = _
  rw [hcard, hcard]
  change _ = (((PMF.uniformOfFintype (MergedPairs F)).filter {M | A M}
    (alignment_supported P hκ a ha bits p)).toOuterMeasure {M | E M}).toReal
  rw [Balanced.uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Set.mem_ofPred_eq]
  change _ = (Fintype.card {M : {M : MergedPairs F // A M} // E M} : ℝ) /
    Fintype.card {M : MergedPairs F // A M}
  rw [hnum]
  have htotal : (Fintype.card (MergedPairs F) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  have hcardinst (f g : Fintype {M : MergedPairs F // A M ∧ E M}) :
      @Fintype.card _ f = @Fintype.card _ g := by
    cases Subsingleton.elim f g
    rfl
  exact congrArg (Nat.cast : ℕ → ℝ) (hcardinst _ _)

end
end Balanced.Local.AlignedUnused

end OAI
