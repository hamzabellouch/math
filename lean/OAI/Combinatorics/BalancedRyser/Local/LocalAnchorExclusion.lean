import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local.AnchorExclusion

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (M : MergedPairs F)

def Purposeful (c : Fin (4 * b - κ)) (ij : Fin b × Fin 4) : Prop :=
  P.classOf ij.1 ij.2 = c ∨ P.classOf ij.1 (ij.2 + 1) = c

omit [Field F] [Fintype F] [DecidableEq F] in
theorem adjacent_generator_ne (ha : Eligible P a) (i : Fin b) (j : Fin 4) :
    a.2 (P.classOf i j) ≠ a.2 (P.classOf i (j + 1)) := by
  intro h
  have heq := P.withinTuple i (ha.2.1 h)
  have hne : j ≠ j + 1 := by fin_cases j <;> decide
  exact hne heq

omit [Fintype F] [DecidableEq F] in
theorem prescribedPoint_on_left (ha : Eligible P a) (i : Fin b) (j : Fin 4) :
    OnLine (prescribedPoint P a bits M (i, j))
      (constituent M (a.2 (P.classOf i j)) (bits i j)) := by
  exact onLine_lineIntersection_left _ _ (adjacent_generator_ne P a ha i j)

omit [Fintype F] [DecidableEq F] in
theorem prescribedPoint_on_right (ha : Eligible P a) (i : Fin b) (j : Fin 4) :
    OnLine (prescribedPoint P a bits M (i, j))
      (constituent M (a.2 (P.classOf i (j + 1))) (!(bits i (j + 1)))) := by
  exact onLine_lineIntersection_right _ _ (adjacent_generator_ne P a ha i j)

theorem purposeful_mem_merged (ha : Eligible P a)
    {c : Fin (4 * b - κ)} {ij : Fin b × Fin 4} (h : Purposeful P c ij) :
    prescribedPoint P a bits M ij ∈ mergedPoints M (a.2 c) := by
  have hex : ∃ s, OnLine (prescribedPoint P a bits M ij)
      (constituent M (a.2 c) s) := by
    rcases h with h | h
    · exact ⟨bits ij.1 ij.2, h ▸ prescribedPoint_on_left P a bits M ha ij.1 ij.2⟩
    · exact ⟨!(bits ij.1 (ij.2 + 1)),
        h ▸ prescribedPoint_on_right P a bits M ha ij.1 ij.2⟩
  obtain ⟨s, hs⟩ := hex
  cases s <;> simp_all [mergedPoints, linePoints]

theorem mem_merged_iff_purposeful_of_used (ha : Eligible P a)
    (p : Point F) (hA : Admissible P a bits p M)
    (i : Fin b) (c : Fin (4 * b - κ))
    (hused : ∃ r, P.classOf i r = c) (j : Fin 4) :
    prescribedPoint P a bits M (i, j) ∈ mergedPoints M (a.2 c) ↔
      Purposeful P c (i, j) := by
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := hused
    have hx' : ∃ s, OnLine (prescribedPoint P a bits M (i, j))
        (constituent M (a.2 c) s) := by
      simpa only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, Bool.exists_bool] using hx
    obtain ⟨s, hs⟩ := hx'
    have hlines : lineThrough (a.1 i) p ≠ constituent M (a.2 c) s := by
      intro heq
      have hd := congrArg Prod.fst heq
      exact ha.2.2 i r (hr ▸ hd.symm)
    by_cases hside : s = bits i r
    · have he : OnLine (prescribedPoint P a bits M (i, r))
          (constituent M (a.2 c) s) := by
        simpa only [hr, hside] using prescribedPoint_on_left P a bits M ha i r
      have hpoint := common_point_eq_of_lines_ne _ _ hlines
        (prescribedPoint P a bits M (i, j)) (prescribedPoint P a bits M (i, r))
        (hA.1 (i, j)) hs (hA.1 (i, r)) he
      have hj : j = r := congrArg Prod.snd (hA.2.1 hpoint)
      exact Or.inl (hj ▸ hr)
    · have hside' : s = !(bits i r) := by
        cases s <;> cases h : bits i r <;> simp_all
      have he : OnLine (prescribedPoint P a bits M (i, r - 1))
          (constituent M (a.2 c) s) := by
        simpa only [sub_add_cancel, hr, hside'] using
          prescribedPoint_on_right P a bits M ha i (r - 1)
      have hpoint := common_point_eq_of_lines_ne _ _ hlines
        (prescribedPoint P a bits M (i, j)) (prescribedPoint P a bits M (i, r - 1))
        (hA.1 (i, j)) hs (hA.1 (i, r - 1)) he
      have hj : j = r - 1 := congrArg Prod.snd (hA.2.1 hpoint)
      right
      simpa only [hj, sub_add_cancel] using hr
  · exact purposeful_mem_merged P a bits M ha

theorem ordinary_line_no_shared_constituent (p : Point F)
    (hA : Admissible P a bits p M) (l : Line F)
    (hl : AllowedPiece a p M (Sum.inr (Sum.inl l)))
    {ij kl : Fin b × Fin 4} (hne : ij ≠ kl) (d : Direction F) (s : Bool)
    (hi : OnLine (prescribedPoint P a bits M ij) (constituent M d s))
    (hk : OnLine (prescribedPoint P a bits M kl) (constituent M d s)) :
    ¬ (OnLine (prescribedPoint P a bits M ij) l ∧
      OnLine (prescribedPoint P a bits M kl) l) := by
  rintro ⟨hil, hkl⟩
  have hpoint : prescribedPoint P a bits M ij ≠ prescribedPoint P a bits M kl :=
    fun h => hne (hA.2.1 h)
  have heq := eq_of_two_common_points _ _ hpoint l (constituent M d s)
    hil hkl hi hk
  apply hl
  rw [heq]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨(d, s), Finset.mem_univ _, rfl⟩)

omit [Fintype F] [DecidableEq F] in

theorem class_eq_of_shared_constituents (ha : Eligible P a)
    {x y : Point F} (hxy : x ≠ y) (c e : Fin (4 * b - κ)) (s t : Bool)
    (hxc : OnLine x (constituent M (a.2 c) s))
    (hyc : OnLine y (constituent M (a.2 c) s))
    (hxe : OnLine x (constituent M (a.2 e) t))
    (hye : OnLine y (constituent M (a.2 e) t)) : c = e := by
  apply ha.2.1
  exact congrArg Prod.fst (eq_of_two_common_points x y hxy _ _ hxc hyc hxe hye)

theorem used_pair_no_self_anchor (ha : Eligible P a) (p : Point F)
    (hA : Admissible P a bits p M) {ij kl : Fin b × Fin 4} (hne : ij ≠ kl)
    (c e : Fin (4 * b - κ)) (s t : Bool)
    (hnc : ¬ Purposeful P c ij) (he : Purposeful P e ij)
    (hie : OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 e) t))
    (hke : OnLine (prescribedPoint P a bits M kl) (constituent M (a.2 e) t)) :
    ¬ (OnLine (prescribedPoint P a bits M ij) (constituent M (a.2 c) s) ∧
      OnLine (prescribedPoint P a bits M kl) (constituent M (a.2 c) s)) := by
  rintro ⟨hic, hkc⟩
  have hpoint : prescribedPoint P a bits M ij ≠ prescribedPoint P a bits M kl :=
    fun h => hne (hA.2.1 h)
  have hce := class_eq_of_shared_constituents P a M ha hpoint c e s t hic hkc hie hke
  exact hnc (hce.symm ▸ he)

end
end Balanced.Local.AnchorExclusion

end OAI
