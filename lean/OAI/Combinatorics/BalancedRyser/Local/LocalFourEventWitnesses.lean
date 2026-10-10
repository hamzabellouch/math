import OAI.Combinatorics.BalancedRyser.Local.LocalFourEvents

namespace OAI

namespace Balanced.Local.FourEvents

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

omit [Fintype F] [DecidableEq F] in

theorem common_line_eq_target_of_same_tuple (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M)
    (i j : Fin b × Fin 4) (hij : i.1 = j.1)
    (hne : prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j)
    (l : Line F) (hi : OnLine (prescribedPoint P a bits M i) l)
    (hj : OnLine (prescribedPoint P a bits M j) l) :
    l = lineThrough (a.1 i.1) p := by
  apply eq_of_two_common_points _ _ hne l _ hi hj (hal i)
  simpa only [hij] using hal j

theorem forbiddenCollinearTriple_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M)
    (h : ForbiddenCollinearTriple P a bits p M) :
    ∃ (l : Line F) (i j k : Fin b × Fin 4),
      i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
      OnLine (prescribedPoint P a bits M i) l ∧
      OnLine (prescribedPoint P a bits M j) l ∧
      OnLine (prescribedPoint P a bits M k) l ∧
      (∀ t, l ≠ lineThrough (a.1 t) p) ∧
      (∀ c s, l ≠ constituent M (a.2 c) s) := by
  obtain ⟨l, htarget, hconst, hcard⟩ := h
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ :=
    Finset.two_lt_card_iff.mp (show 2 <
      (prescribedDesignated P a bits M ∩ linePoints l).card by omega)
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).1
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hy).1
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).1
  have hi := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hj := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  have hk := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
  refine ⟨l,i,j,k,?_,?_,?_,hxy,hxz,hyz,hi,hj,hk,htarget,hconst⟩
  · intro hij
    exact htarget i.1 (common_line_eq_target_of_same_tuple P a bits p M hal i j hij hxy l hi hj)
  · intro hik
    exact htarget i.1 (common_line_eq_target_of_same_tuple P a bits p M hal i k hik hxz l hi hk)
  · intro hjk
    exact htarget j.1 (common_line_eq_target_of_same_tuple P a bits p M hal j k hjk hyz l hj hk)

theorem usedPairExtra_iff_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (ha : Function.Injective a.2) :
    UsedPairExtra P a bits M ↔
      ∃ (c : Fin (4 * b - κ)) (i : Fin b × Fin 4) (s : Bool),
        (∀ j, P.classOf i.1 j ≠ c) ∧
        OnLine (prescribedPoint P a bits M i) (constituent M (a.2 c) s) := by
  constructor
  · rintro ⟨d, hd, i, hn, x, hx, hmerged⟩
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j, rfl⟩ := (mem_tuplePoints P a bits M i x).mp hx
    have hnclass : ∀ k, P.classOf i k ≠ c := by
      intro k hk
      apply hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, congrArg a.2 hk⟩
    rcases Finset.mem_union.mp hmerged with hleft | hright
    · exact ⟨c,(i,j),false,hnclass,(Finset.mem_filter.mp hleft).2⟩
    · exact ⟨c,(i,j),true,hnclass,(Finset.mem_filter.mp hright).2⟩
  · rintro ⟨c,⟨i,j⟩,s,hn,hpoint⟩
    refine ⟨a.2 c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
      i, ?_, prescribedPoint P a bits M (i,j), ?_, ?_⟩
    · intro hi
      obtain ⟨k,hk⟩ := (Finset.mem_filter.mp hi).2
      exact hn k (ha hk)
    · exact (mem_tuplePoints P a bits M i _).mpr ⟨j,rfl⟩
    · have hm : prescribedPoint P a bits M (i,j) ∈ linePoints (constituent M (a.2 c) s) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoint⟩
      cases s
      · exact Finset.mem_union_left _ hm
      · exact Finset.mem_union_right _ hm

omit [Fintype F] in

theorem unusedPrecoverage_iff_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F) (M : MergedPairs F) :
    UnusedPrecoverage P a bits p M ↔
      ∃ (d : Direction F) (s : Bool) (i : Fin b × Fin 4),
        d ∉ usedDirections a ∧ OnLine p (constituent M d s) ∧
        OnLine (prescribedPoint P a bits M i) (constituent M d (!s)) := by
  constructor
  · rintro ⟨d,hd,s,hp,x,hx,hpoint⟩
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨d,s,i,hd,hp,hpoint⟩
  · rintro ⟨d,s,i,hd,hp,hpoint⟩
    exact ⟨d,hd,s,hp,prescribedPoint P a bits M i,
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hpoint⟩

theorem forbiddenCollinearTriple_joiningLine (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hal : Aligned P a bits p M)
    (h : ForbiddenCollinearTriple P a bits p M) :
    ∃ i j k : Fin b × Fin 4,
      i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
      OnLine (prescribedPoint P a bits M k)
        (joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j)) ∧
      (∀ t, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
        lineThrough (a.1 t) p) ∧
      (∀ c s, joiningLine (prescribedPoint P a bits M i) (prescribedPoint P a bits M j) ≠
        constituent M (a.2 c) s) := by
  obtain ⟨l,i,j,k,hij,hik,hjk,hxy,hxz,hyz,hi,hj,hk,htarget,hconst⟩ :=
    forbiddenCollinearTriple_indices P a bits p M hal h
  have hl : l = joiningLine (prescribedPoint P a bits M i)
      (prescribedPoint P a bits M j) :=
    eq_of_two_common_points _ _ hxy _ _ hi hj
      (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)
  subst l
  exact ⟨i,j,k,hij,hik,hjk,hxy,hxz,hyz,hk,htarget,hconst⟩

theorem unusedNoncollinearTriple_indices (P : EqualityPattern b κ)
    (a : DirectionAssignment F b κ) (bits : Bits b) (M : MergedPairs F)
    (h : UnusedNoncollinearTriple P a bits M) :
    ∃ (d : Direction F) (i j k : Fin b × Fin 4), d ∉ usedDirections a ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M j ∧
      prescribedPoint P a bits M i ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M j ≠ prescribedPoint P a bits M k ∧
      prescribedPoint P a bits M i ∈ mergedPoints M d ∧
      prescribedPoint P a bits M j ∈ mergedPoints M d ∧
      prescribedPoint P a bits M k ∈ mergedPoints M d ∧
      ¬ ∃ l : Line F, OnLine (prescribedPoint P a bits M i) l ∧
        OnLine (prescribedPoint P a bits M j) l ∧
        OnLine (prescribedPoint P a bits M k) l := by
  obtain ⟨d,hd,U,hcard,hU,hnline⟩ := h
  obtain ⟨x,y,z,hxy,hxz,hyz,hUeq⟩ := Finset.card_eq_three.mp hcard
  have hx : x ∈ U := by rw [hUeq]; simp
  have hy : y ∈ U := by rw [hUeq]; simp
  have hz : z ∈ U := by rw [hUeq]; simp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hU hx)).1
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hU hy)).1
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hU hz)).1
  refine ⟨d,i,j,k,hd,hxy,hxz,hyz,(Finset.mem_inter.mp (hU hx)).2,
    (Finset.mem_inter.mp (hU hy)).2,(Finset.mem_inter.mp (hU hz)).2,?_⟩
  rintro ⟨l,hi,hj,hk⟩
  apply hnline
  refine ⟨l,?_⟩
  intro x hxU
  rw [hUeq] at hxU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxU
  rcases hxU with rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩

end
end Balanced.Local.FourEvents

end OAI
