import OAI.Combinatorics.BalancedRyser.Local.LocalConditionSpec
import OAI.Combinatorics.BalancedRyser.Local.LocalFiberBounds

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open LocalFiberBounds

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

def PointHolds (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) (v : Position b) :
    Code b κ → Prop
  | Sum.inl _ => ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
      ∃ t : Bool, OnLine p (constituent M d t) ∧
        OnLine (x v) (constituent M d (!t)) ∧
        constituent M d (!t) ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inl xy) => x xy.1 ≠ x xy.2 ∧
      OnLine (x v) (joiningLine (x xy.1) (x xy.2)) ∧
      joiningLine (x xy.1) (x xy.2) ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inl w)) =>
      ∃ d : Direction F, d ∉ FourEvents.usedDirections a ∧
        x w ∈ mergedPoints M d ∧
        ∃ t : Bool, OnLine (x v) (constituent M d t) ∧
          constituent M d t ≠ lineThrough (a.1 v.1) p
  | Sum.inr (Sum.inr (Sum.inr cw)) =>
      OnLine (x v) (lineThrough (a.2 cw.1) (x cw.2)) ∧
      lineThrough (a.2 cw.1) (x cw.2) ≠ lineThrough (a.1 v.1) p

theorem holds_eq_pointHolds (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (v : Position b) (z : Code b κ) :
    Holds P a bits p M v z =
      PointHolds a p M (prescribedPoint P a bits M) v z := by
  cases z with
  | inl z => rfl
  | inr z => cases z with
    | inl z => rfl
    | inr z => cases z <;> rfl

def unusedDirections (a : DirectionAssignment F b κ) : Finset (Direction F) :=
  Finset.univ \ FourEvents.usedDirections a

def testLines (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) : Code b κ → Finset (Line F)
  | Sum.inl _ => partnerCandidates M (unusedDirections a) p
  | Sum.inr (Sum.inl xy) => {joiningLine (x xy.1) (x xy.2)}
  | Sum.inr (Sum.inr (Sum.inl w)) => mergedCandidates M (unusedDirections a) (x w)
  | Sum.inr (Sum.inr (Sum.inr cw)) => {lineThrough (a.2 cw.1) (x cw.2)}

theorem pointHolds_imp_testLines (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) (v : Position b) (z : Code b κ)
    (h : PointHolds a p M x v z) :
    ∃ l ∈ testLines a p M x z, l ≠ lineThrough (a.1 v.1) p ∧ OnLine (x v) l := by
  rcases z with u | xy | w | cw
  · obtain ⟨d, hd, t, hp, hv, hn⟩ := h
    exact ⟨constituent M d (!t), partner_mem_partnerCandidates M _ p d t
      (by simpa [unusedDirections] using hd) hp, hn, hv⟩
  · exact ⟨joiningLine (x xy.1) (x xy.2), by simp [testLines], h.2.2, h.2.1⟩
  · obtain ⟨d, hd, hw, t, hv, hn⟩ := h
    have hw' : ∃ s : Bool, OnLine (x w) (constituent M d s) := by
      simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, Bool.exists_bool] using hw
    obtain ⟨s, hs⟩ := hw'
    exact ⟨constituent M d t, constituent_mem_mergedCandidates M _ (x w) d s t
      (by simpa [unusedDirections] using hd) hs, hn, hv⟩
  · exact ⟨lineThrough (a.2 cw.1) (x cw.2), by simp [testLines], h.2, h.1⟩

theorem testLines_card_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x : Position b → Point F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (z : Code b κ) : (testLines a p M x z).card ≤ 2 * B := by
  rcases z with u | xy | w | cw
  · exact (card_partnerCandidates_le M _ p B (hmult p)).trans (by omega)
  · simp only [testLines, Finset.card_singleton]; omega
  · exact card_mergedCandidates_le M _ (x w) B (hmult (x w))
  · simp only [testLines, Finset.card_singleton]; omega

theorem testLines_congr (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x y : Position b → Point F) (z : Code b κ)
    (h : ∀ w ∈ anchors z, x w = y w) :
    testLines a p M x z = testLines a p M y z := by
  rcases z with u | xy | w | cw
  · rfl
  · simp only [testLines, h xy.1 (by simp [anchors]), h xy.2 (by simp [anchors])]
  · simp only [testLines, h w (by simp [anchors])]
  · simp only [testLines, h cw.2 (by simp [anchors])]

theorem pointHolds_congr (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (x y : Position b → Point F) (v : Position b) (z : Code b κ)
    (hv : x v = y v) (h : ∀ w ∈ anchors z, x w = y w) :
    PointHolds a p M x v z ↔ PointHolds a p M y v z := by
  rcases z with u | xy | w | cw
  · simp only [PointHolds, hv]
  · simp only [PointHolds, hv, h xy.1 (by simp [anchors]), h xy.2 (by simp [anchors])]
  · simp only [PointHolds, hv, h w (by simp [anchors])]
  · simp only [PointHolds, hv, h cw.2 (by simp [anchors])]

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem pointHolds_fiber_card_le (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (x : α → F) (i : α) (v : Position b) (z : Code b κ)
    (hown : u v = i) (hanchor : ∀ w ∈ anchors z, u w ≠ i)
    (hinj : Function.Injective (point v))
    (hline : ∀ t, OnLine (point v t) (lineThrough (a.1 v.1) p)) :
    (Finset.univ.filter (fun t : F => PointHolds a p M
      (fun w => point w (Function.update x i t (u w))) v z)).card ≤ 2 * B := by
  let S := lineThrough (a.1 v.1) p
  let L := testLines a p M (fun w => point w (x (u w))) z
  have hsub : Finset.univ.filter (fun t : F => PointHolds a p M
      (fun w => point w (Function.update x i t (u w))) v z) ⊆
      Finset.univ.filter (fun t : F => ∃ l ∈ L.erase S, OnLine (point v t) l) := by
    intro t ht
    obtain ⟨l, hl, hn, hv⟩ := pointHolds_imp_testLines a p M _ v z
      (Finset.mem_filter.mp ht).2
    have heq : testLines a p M
        (fun w => point w (Function.update x i t (u w))) z = L := by
      apply testLines_congr
      intro w hw
      simp only [Function.update_of_ne (hanchor w hw)]
    rw [heq] at hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, l,
      Finset.mem_erase.mpr ⟨hn, hl⟩, by simpa [hown] using hv⟩
  exact (Finset.card_le_card hsub).trans
    ((line_union_fiber_card_le S (L.erase S) (point v) hinj hline
      (fun l hl => (Finset.mem_erase.mp hl).1)).trans
      ((Finset.card_le_card (Finset.erase_subset S L)).trans
        (testLines_card_le a p M _ B hB hmult z)))

omit [Fintype α] in
theorem pointHolds_update_iff (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (u : Position b → α) (point : Position b → F → Point F)
    (x : α → F) (j : α) (t : F) (v : Position b) (z : Code b κ)
    (hown : u v ≠ j) (hanchor : ∀ w ∈ anchors z, u w ≠ j) :
    PointHolds a p M (fun w => point w (Function.update x j t (u w))) v z ↔
      PointHolds a p M (fun w => point w (x (u w))) v z := by
  apply pointHolds_congr
  · simp only [Function.update_of_ne hown]
  · intro w hw
    simp only [Function.update_of_ne (hanchor w hw)]

theorem pointHolds_product_bound (a : DirectionAssignment F b κ) (p : Point F)
    (M : MergedPairs F) (B : ℕ) (hB : 1 ≤ B)
    (hmult : ∀ y : Point F, (indexedThrough M (unusedDirections a) y).card ≤ B)
    (u : Position b → α) (point : Position b → F → Point F)
    (s : Finset α) (test : α → Position b) (code : α → Code b κ)
    (rank : α → ℕ)
    (hown : ∀ i ∈ s, u (test i) = i)
    (hanchor : ∀ i ∈ s, ∀ w ∈ anchors (code i), u w ≠ i)
    (hinj : ∀ i ∈ s, Function.Injective (point (test i)))
    (hline : ∀ i ∈ s, ∀ t, OnLine (point (test i) t) (lineThrough (a.1 (test i).1) p))
    (hrank : ∀ i ∈ s, ∀ j ∈ s,
      j ∈ (anchors (code i)).image u → rank i < rank j) :
    ((Finset.univ.filter (fun x : α → F => ∀ i ∈ s,
      PointHolds a p M (fun w => point w (x (u w))) (test i) (code i))).card : ℝ) /
      Fintype.card (α → F) ≤ (2 * (B : ℝ) / Fintype.card F) ^ s.card := by
  apply DependencyExtraction.uniform_event_bound_of_dependency_relation
    s (fun i j => j ∈ (anchors (code i)).image u) rank
    (fun i x => PointHolds a p M (fun w => point w (x (u w))) (test i) (code i))
    (2 * (B : ℝ) / Fintype.card F) (by positivity) hrank
  · intro i hi x
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast pointHolds_fiber_card_le a p M B hB hmult u point x i
      (test i) (code i) (hown i hi) (hanchor i hi) (hinj i hi) (hline i hi)
  · intro i hi j hj hij hn x t
    apply pointHolds_update_iff
    · rw [hown i hi]
      exact hij
    · intro w hw heq
      apply hn
      exact Finset.mem_image.mpr ⟨w, hw, heq⟩

end
end Balanced.Local.ConditionSpec

end OAI
