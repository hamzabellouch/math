import OAI.MeasureTheory.Falconer.Estimates.RegularizationCardinality

namespace OAI

namespace PlanarFalconer

noncomputable def prefixFiber (C : Finset CellPath) (a : ℕ) (P : CellPath) : Finset CellPath := by
  classical
  exact C.filter fun q => q.take a = P

noncomputable def prefixChildren (C : Finset CellPath) (a b : ℕ) (P : CellPath) :
    Finset CellPath := (prefixFiber C a P).image (List.take b)

theorem prefixFiber_zero (C : Finset CellPath) : prefixFiber C 0 [] = C := by
  classical
  simp [prefixFiber]

theorem prefixFiber_leaf {N : ℕ} {C : Finset CellPath} (hC : C ⊆ dyadicPaths N)
    {p : CellPath} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {path : CellPath} (hpath : path ∈ C) : path.length = N :=
    (mem_dyadicPaths N path).mp (hC hpath)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_nonempty {C : Finset CellPath} {a : ℕ} {P : CellPath}
    (hP : P ∈ C.image (List.take a)) : (prefixFiber C a P).Nonempty := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  exact ⟨q,by simp [prefixFiber,hq]⟩

theorem prefixChildren_mem_image {C : Finset CellPath} {a b : ℕ} {P q : CellPath}
    (hq : q ∈ prefixChildren C a b P) : q ∈ C.image (List.take b) := by
  classical
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨r,(Finset.mem_filter.mp hr).1,rfl⟩

theorem prefixFiber_parent_filter {C : Finset CellPath} {a b : ℕ} (hab : a ≤ b)
    {P c : CellPath} (hc : c ∈ prefixChildren C a b P) :
    (prefixFiber C a P).filter (fun q => q.take b = c) = prefixFiber C b c := by
  classical
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hc
  have hr := (Finset.mem_filter.mp hr).2
  ext q
  simp only [prefixFiber, Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hq,he⟩
    exact ⟨⟨hq,(take_eq_of_take_eq hab he).trans hr⟩,he⟩

theorem prefixFiber_card_sum {C : Finset CellPath} {a b : ℕ} (hab : a ≤ b)
    (P : CellPath) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

theorem prefixFiber_count_bounds {C : Finset CellPath} {a b lo hi B : ℕ}
    (hab : a ≤ b) (P : CellPath)
    (hbranch : B ≤ (prefixChildren C a b P).card ∧ (prefixChildren C a b P).card ≤ 2*B)
    (hchild : ∀ c ∈ prefixChildren C a b P,
      lo ≤ (prefixFiber C b c).card ∧ (prefixFiber C b c).card ≤ hi) :
    B*lo ≤ (prefixFiber C a P).card ∧ (prefixFiber C a P).card ≤ 2*B*hi := by
  classical
  rw [prefixFiber_card_sum hab]
  constructor
  · calc
      B*lo ≤ (prefixChildren C a b P).card*lo := Nat.mul_le_mul_right _ hbranch.1
      _ = ∑ _c ∈ prefixChildren C a b P, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (hchild c hc).1)
  · calc
      _ ≤ ∑ _c ∈ prefixChildren C a b P, hi := Finset.sum_le_sum (fun c hc => (hchild c hc).2)
      _ = (prefixChildren C a b P).card*hi := by simp
      _ ≤ 2*B*hi := Nat.mul_le_mul_right _ hbranch.2

theorem prefixChildren_class_eq (L : Finset CellPath) (F : CellPath → List ℕ)
    (a b : ℕ) {T : List ℕ} {p : CellPath} (hp : p ∈ classLeaves L F T) :
    prefixChildren (classLeaves L F T) a b (p.take a) = labeledChildren L F a b p := by
  classical
  have hFp := (Finset.mem_filter.mp hp).2
  apply congrArg (Finset.image (List.take b))
  ext q
  simp only [prefixFiber, classLeaves, Finset.mem_filter, hFp]
  tauto

end PlanarFalconer

end OAI
