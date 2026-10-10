import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalProduct
import OAI.Combinatorics.BalancedRyser.Local.LocalPrescribedGeometry

namespace OAI

namespace Balanced.Local.AlignedGlobal

open RootChildPartition TupleAlignment PrescribedGeometry
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ}

private def lineScalar (g : Direction F) (x : Point F) : F :=
  match g with | none => x.2 | some _ => x.1

omit [Fintype F] [DecidableEq F] in
private theorem linePointEquiv_coordinate (g : Direction F) (c : F)
    (x : {y : Point F // OnLine y (g,c)}) :
    linePointEquiv g c x = lineScalar g x.1 := by
  cases g <;> rfl

omit [Fintype F] in

theorem free_point_eq_of_scalar_eq (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (ij : FreeIndex P R)
    (hx : (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij)
    (ht : a.1 ij.1.1 = a'.1 ij.1.1) :
    prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a' bits N.1 ij.1 := by
  have h := hx
  change linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩ =
    linePointEquiv (a'.1 ij.1.1) (lineEval (a'.1 ij.1.1) p)
      ⟨prescribedPoint P a' bits N.1 ij.1, N.2 ij.1⟩ at h
  have hn : OnLine (prescribedPoint P a' bits N.1 ij.1)
      (lineThrough (a.1 ij.1.1) p) := by simpa only [ht] using N.2 ij.1
  let yn : {x : Point F // OnLine x (lineThrough (a.1 ij.1.1) p)} :=
    ⟨prescribedPoint P a' bits N.1 ij.1, hn⟩
  have h' : linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)
      ⟨prescribedPoint P a bits M.1 ij.1, M.2 ij.1⟩ =
    linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p) yn := by
    erw [linePointEquiv_coordinate, linePointEquiv_coordinate] at h ⊢
    simpa only [yn, ht] using h
  exact congrArg Subtype.val ((linePointEquiv _ _).injective h')

omit [Fintype F] in
theorem free_point_eq_of_coordinate_eq (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ij : FreeIndex P R) (ht : a.1 ij.1.1 = a'.1 ij.1.1) :
    prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a' bits N.1 ij.1 :=
  free_point_eq_of_scalar_eq P R a a' bits p M N ij (congrFun hx ij) ht

omit [Fintype F] [DecidableEq F] in

theorem generator_offsets_eq_of_points (P : EqualityPattern b κ)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (M N : MergedPairs F) (i : Fin b) (j : Fin 4)
    (hd : a.2 (P.classOf i j) = a'.2 (P.classOf i j))
    (hp : ∀ k, prescribedPoint P a bits M (i,k) =
      prescribedPoint P a' bits N (i,k)) :
    M (a.2 (P.classOf i j)) = N (a'.2 (P.classOf i j)) := by
  funext s
  by_cases hs : s = bits i j
  · have hm := prescribedPoint_on_left (M := M) (bits := bits) ha i j
    have hn := prescribedPoint_on_left (M := N) (bits := bits) ha' i j
    dsimp only [OnLine, constituent] at hm hn
    rw [hd, hp j] at hm
    simpa only [hs, hd] using hm.symm.trans hn
  · have hs' : s = !(bits i j) := by cases s <;> cases h : bits i j <;> simp_all
    have hm := prescribedPoint_on_right (M := M) (bits := bits) ha i (j-1)
    have hn := prescribedPoint_on_right (M := N) (bits := bits) ha' i (j-1)
    have hj : j - 1 + 1 = j := sub_add_cancel j 1
    dsimp only [OnLine, constituent] at hm hn
    simp only [hj] at hm hn
    rw [hd, hp (j-1)] at hm
    simpa only [hs', hd] using hm.symm.trans hn

omit [Fintype F] in
theorem root_offsets_eq_of_coordinates (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (ha : Eligible P a) (ha' : Eligible P a') (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ R, a.1 i = a'.1 i)
    (c : Fin (4*b-κ)) (hc : c ∈ R.biUnion P.classSet)
    (hd : a.2 c = a'.2 c) : M.1 (a.2 c) = N.1 (a'.2 c) := by
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
  apply generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 i j hd
  intro k
  apply free_point_eq_of_coordinate_eq P R a a' bits p M N hx
    ⟨(i,k), ?_⟩ (ht i hi)
  simp only [mem_dependentOccurrences, not_and]
  exact fun hnot => (hnot hi).elim

omit [Fintype F] in
theorem point_eq_of_root_history (P : EqualityPattern b κ)
    (R : Finset (Fin b)) (a a' : DirectionAssignment F b κ)
    (ha : Eligible P a) (ha' : Eligible P a') (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ R, a.1 i = a'.1 i)
    (hd : ∀ c ∈ R.biUnion P.classSet, a.2 c = a'.2 c)
    (ij : Fin b × Fin 4) (hi : a.1 ij.1 = a'.1 ij.1) :
    prescribedPoint P a bits M.1 ij = prescribedPoint P a' bits N.1 ij := by
  by_cases hdep : ij ∈ dependentOccurrences P R
  · have hdep' := (mem_dependentOccurrences P R ij).mp hdep
    have htarget : lineEval (a.1 ij.1) (prescribedPoint P a bits M.1 ij) =
        lineEval (a.1 ij.1) (prescribedPoint P a' bits N.1 ij) := by
      have hm := M.2 ij
      have hn := N.2 ij
      change lineEval _ _ = _ at hm hn
      rw [hi] at hm ⊢
      exact hm.trans hn.symm
    rcases hdep'.2 with hl | hr
    · apply (lineEvalEquiv (a.2 (P.classOf ij.1 ij.2)) (a.1 ij.1)
        (ha.2.2 ij.1 ij.2)).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_left (M := M.1) (bits := bits) ha ij.1 ij.2
        have hn := prescribedPoint_on_left (M := N.1) (bits := bits) ha' ij.1 ij.2
        have ho := root_offsets_eq_of_coordinates P R a a' ha ha' bits p M N hx ht
          _ hl (hd _ hl)
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, ho, hd _ hl]
        exact hn.symm
      · exact htarget
    · apply (lineEvalEquiv (a.2 (P.classOf ij.1 (ij.2+1))) (a.1 ij.1)
        (ha.2.2 ij.1 (ij.2+1))).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_right (M := M.1) (bits := bits) ha ij.1 ij.2
        have hn := prescribedPoint_on_right (M := N.1) (bits := bits) ha' ij.1 ij.2
        have ho := root_offsets_eq_of_coordinates P R a a' ha ha' bits p M N hx ht
          _ hr (hd _ hr)
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, ho, hd _ hr]
        exact hn.symm
      · exact htarget
  · exact free_point_eq_of_coordinate_eq P R a a' bits p M N hx ⟨ij,hdep⟩ hi

omit [Fintype F] in
theorem history_points_eq (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j) := by
  intro i hi j
  by_cases hir : i ∈ R
  · apply free_point_eq_of_coordinate_eq P R a a' bits p M N hx
      ⟨(i,j), ?_⟩ (ht i hi)
    simp only [mem_dependentOccurrences, not_and]
    exact fun hn => (hn hir).elim
  · apply point_eq_of_root_history P R a a' ha ha' bits p M N hx
      (fun r hr => ht r (hclosed i hi hir hr)) ?_ (i,j) (ht i hi)
    intro c hc
    apply hd c
    obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨r, hclosed i hi hir hr, hcr⟩

omit [Fintype F] in
theorem history_offsets_eq (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : (coordinates P R a bits p M).1 = (coordinates P R a' bits p N).1)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c) := by
  intro c hc
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
  exact generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 i j
    (hd _ hc) (history_points_eq P R S hclosed a a' ha ha' bits p M N hx ht hd i hi)

theorem inverse_coordinates_fst_eq (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a') :
    (coordinates P R a bits p
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u))).1 =
    (coordinates P R a' bits p
      ((coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u'))).1 := by
  change ((coordinateEquiv P hκ R hD a ha bits p)
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u))).1 =
    ((coordinateEquiv P hκ R hD a' ha' bits p)
      ((coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u'))).1
  simp only [Equiv.apply_symm_apply]

theorem root_closed_of_prefix (R S : Finset (Fin b))
    (hS : S ⊆ R ∨ R ⊆ S) : ∀ i ∈ S, i ∉ R → R ⊆ S := by
  intro i hi hn
  rcases hS with hS | hS
  · exact False.elim (hn (hS hi))
  · exact hS

theorem generated_history_agree (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a')
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
    let N := (coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u')
    (∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j)) ∧
    (∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c)) := by
  dsimp only
  have hx := inverse_coordinates_fst_eq P hκ R hD a a' ha ha' bits p x u u'
  exact ⟨history_points_eq P R S (root_closed_of_prefix R S hS) a a' ha ha'
      bits p _ _ hx ht hd,
    history_offsets_eq P R S (root_closed_of_prefix R S hS) a a' ha ha'
      bits p _ _ hx ht hd⟩

theorem generated_point_eq_of_root_history (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a')
    (ht : ∀ i ∈ R, a.1 i = a'.1 i)
    (hd : ∀ c ∈ R.biUnion P.classSet, a.2 c = a'.2 c)
    (ij : Fin b × Fin 4) (hi : a.1 ij.1 = a'.1 ij.1) :
    prescribedPoint P a bits
      ((coordinateEquiv P hκ R hD a ha bits p).symm (x,u)).1 ij =
    prescribedPoint P a' bits
      ((coordinateEquiv P hκ R hD a' ha' bits p).symm (x,u')).1 ij :=
  point_eq_of_root_history P R a a' ha ha' bits p _ _
    (inverse_coordinates_fst_eq P hκ R hD a a' ha ha' bits p x u u') ht hd ij hi

omit [Fintype F] in
theorem history_points_eq_of_coordinates_on (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : ∀ ij : FreeIndex P R, ij.1.1 ∈ S →
      (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j) := by
  have hf (ij : FreeIndex P R) (hi : ij.1.1 ∈ S) :
      prescribedPoint P a bits M.1 ij.1 = prescribedPoint P a' bits N.1 ij.1 :=
    free_point_eq_of_scalar_eq P R a a' bits p M N ij (hx ij hi) (ht _ hi)
  intro i hi j
  by_cases hdep : (i,j) ∈ dependentOccurrences P R
  · have hh := (mem_dependentOccurrences P R (i,j)).mp hdep
    have hRS : R ⊆ S := hclosed i hi hh.1
    have hCS : R.biUnion P.classSet ⊆ S.biUnion P.classSet := by
      intro c hc
      obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_biUnion.mpr ⟨r, hRS hr, hcr⟩
    have hold (c : Fin (4*b-κ)) (hc : c ∈ R.biUnion P.classSet) :
        M.1 (a.2 c) = N.1 (a'.2 c) := by
      obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hcr
      apply generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 r k
        (hd _ (hCS hc))
      intro l
      apply hf ⟨(r,l), ?_⟩ (hRS hr)
      simp only [mem_dependentOccurrences, not_and]
      exact fun hn => (hn hr).elim
    have htarget : lineEval (a.1 i) (prescribedPoint P a bits M.1 (i,j)) =
        lineEval (a.1 i) (prescribedPoint P a' bits N.1 (i,j)) := by
      have hm := M.2 (i,j)
      have hn := N.2 (i,j)
      change lineEval _ _ = _ at hm hn
      rw [ht i hi] at hm ⊢
      exact hm.trans hn.symm
    rcases hh.2 with hl | hr
    · apply (lineEvalEquiv (a.2 (P.classOf i j)) (a.1 i) (ha.2.2 i j)).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_left (M := M.1) (bits := bits) ha i j
        have hn := prescribedPoint_on_left (M := N.1) (bits := bits) ha' i j
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, hold _ hl, hd _ (hCS hl)]
        exact hn.symm
      · exact htarget
    · apply (lineEvalEquiv (a.2 (P.classOf i (j+1))) (a.1 i)
        (ha.2.2 i (j+1))).injective
      apply Prod.ext
      · have hm := prescribedPoint_on_right (M := M.1) (bits := bits) ha i j
        have hn := prescribedPoint_on_right (M := N.1) (bits := bits) ha' i j
        dsimp only [OnLine, constituent] at hm hn
        change lineEval _ _ = lineEval _ _
        rw [hm, hold _ hr, hd _ (hCS hr)]
        exact hn.symm
      · exact htarget
  · exact hf ⟨(i,j),hdep⟩ hi

omit [Fintype F] in
theorem history_offsets_eq_of_coordinates_on (P : EqualityPattern b κ)
    (R S : Finset (Fin b)) (hclosed : ∀ i ∈ S, i ∉ R → R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F)
    (M : AlignedOffsets P a bits p) (N : AlignedOffsets P a' bits p)
    (hx : ∀ ij : FreeIndex P R, ij.1.1 ∈ S →
      (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij)
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    ∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c) := by
  intro c hc
  obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hj
  exact generator_offsets_eq_of_points P a a' ha ha' bits M.1 N.1 i j
    (hd _ hc) (history_points_eq_of_coordinates_on P R S hclosed
      a a' ha ha' bits p M N hx ht hd i hi)

theorem generated_history_agree_on (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a a' : DirectionAssignment F b κ) (ha : Eligible P a) (ha' : Eligible P a')
    (bits : Bits b) (p : Point F) (x y : FreeIndex P R → F)
    (hxy : ∀ ij : FreeIndex P R, ij.1.1 ∈ S → x ij = y ij)
    (u : AlignedUnused.UnusedArray P a) (u' : AlignedUnused.UnusedArray P a')
    (ht : ∀ i ∈ S, a.1 i = a'.1 i)
    (hd : ∀ c ∈ S.biUnion P.classSet, a.2 c = a'.2 c) :
    let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
    let N := (coordinateEquiv P hκ R hD a' ha' bits p).symm (y,u')
    (∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a' bits N.1 (i,j)) ∧
    (∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a'.2 c)) := by
  let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
  let N := (coordinateEquiv P hκ R hD a' ha' bits p).symm (y,u')
  have hx : ∀ ij : FreeIndex P R, ij.1.1 ∈ S →
      (coordinates P R a bits p M).1 ij = (coordinates P R a' bits p N).1 ij := by
    intro ij hi
    have hm := congrFun (congrArg Prod.fst
      ((coordinateEquiv P hκ R hD a ha bits p).apply_symm_apply (x,u))) ij
    have hn := congrFun (congrArg Prod.fst
      ((coordinateEquiv P hκ R hD a' ha' bits p).apply_symm_apply (y,u'))) ij
    exact hm.trans ((hxy ij hi).trans hn.symm)
  exact ⟨history_points_eq_of_coordinates_on P R S (root_closed_of_prefix R S hS)
      a a' ha ha' bits p M N hx ht hd,
    history_offsets_eq_of_coordinates_on P R S (root_closed_of_prefix R S hS)
      a a' ha ha' bits p M N hx ht hd⟩

theorem generated_history_update (P : EqualityPattern b κ) (hκ : κ ≤ 2)
    (R S : Finset (Fin b)) (hD : (dependentOccurrences P R).card = 2*κ)
    (hS : S ⊆ R ∨ R ⊆ S)
    (a : DirectionAssignment F b κ) (ha : Eligible P a)
    (bits : Bits b) (p : Point F) (x : FreeIndex P R → F)
    (u : AlignedUnused.UnusedArray P a) (v : FreeIndex P R) (hv : v.1.1 ∉ S) (t : F) :
    let M := (coordinateEquiv P hκ R hD a ha bits p).symm (x,u)
    let N := (coordinateEquiv P hκ R hD a ha bits p).symm (Function.update x v t,u)
    (∀ i ∈ S, ∀ j, prescribedPoint P a bits M.1 (i,j) =
      prescribedPoint P a bits N.1 (i,j)) ∧
    (∀ c ∈ S.biUnion P.classSet, M.1 (a.2 c) = N.1 (a.2 c)) := by
  apply generated_history_agree_on P hκ R S hD hS a a ha ha bits p
    x (Function.update x v t) ?_ u u (fun _ _ => rfl) (fun _ _ => rfl)
  intro ij hi
  have hne : ij ≠ v := by
    intro heq
    exact hv (heq ▸ hi)
  simp only [Function.update_of_ne hne]

end
end Balanced.Local.AlignedGlobal

end OAI
