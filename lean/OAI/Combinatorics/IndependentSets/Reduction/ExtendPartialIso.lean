import Mathlib

namespace OAI

namespace LargeIndependentSets

theorem extend_partialIso {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    [Countable X] [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X] [Nonempty X]
    [Countable Y] [DenselyOrdered Y] [NoMinOrder Y] [NoMaxOrder Y] [Nonempty Y]
    (seed : Order.PartialIso X Y) :
    ∃ e : X ≃o Y, ∀ x y, (x, y) ∈ seed.val → e x = y := by
  classical
  cases nonempty_encodable X
  cases nonempty_encodable Y
  let cof : X ⊕ Y → Order.Cofinal (Order.PartialIso X Y) := fun p =>
    Sum.recOn p (Order.PartialIso.definedAtLeft Y) (Order.PartialIso.definedAtRight X)
  let ideal : Order.Ideal (Order.PartialIso X Y) := Order.idealOfCofinals seed cof
  let F x := Order.PartialIso.funOfIdeal x ideal
    (Order.cofinal_meets_idealOfCofinals seed cof (Sum.inl x))
  let G y := Order.PartialIso.invOfIdeal y ideal
    (Order.cofinal_meets_idealOfCofinals seed cof (Sum.inr y))
  let e := OrderIso.ofCmpEqCmp (fun x => (F x).val) (fun y => (G y).val) (by
    intro x y
    rcases (F x).property with ⟨f, hf, hx⟩
    rcases (G y).property with ⟨g, hg, hy⟩
    rcases ideal.directed _ hf _ hg with ⟨m, _, fm, gm⟩
    exact m.property (x, _) (fm hx) (_, y) (gm hy))
  refine ⟨e, ?_⟩
  intro x y hxy
  rcases (F x).property with ⟨f, hf, hx⟩
  rcases ideal.directed _ (Order.mem_idealOfCofinals seed cof) _ hf with ⟨m, _, sm, fm⟩
  have hh := m.property (x, y) (sm hxy) (x, (F x).val) (fm hx)
  have hresult : y = (F x).val := (eq_iff_eq_of_cmp_eq_cmp hh).mp rfl
  exact hresult.symm

theorem rational_automorphism_fixing (I : Finset ℚ) (a b : ℚ)
    (ha : a ∉ I) (hb : b ∉ I)
    (hcut : ∀ i ∈ I, i < a ↔ i < b) :
    ∃ e : ℚ ≃o ℚ, e a = b ∧ ∀ i ∈ I, e i = i := by
  classical
  have hcmp (i : ℚ) (hi : i ∈ I) : cmp i a = cmp i b := by
    by_cases hia : i < a
    · rw [(cmp_eq_lt_iff i a).mpr hia, (cmp_eq_lt_iff i b).mpr ((hcut i hi).mp hia)]
    · have hai : a < i := lt_of_le_of_ne (le_of_not_gt hia) (fun h => ha (h ▸ hi))
      have hbi : b < i := lt_of_le_of_ne (le_of_not_gt (fun h => hia ((hcut i hi).mpr h)))
        (fun h => hb (h ▸ hi))
      rw [(cmp_eq_gt_iff i a).mpr hai, (cmp_eq_gt_iff i b).mpr hbi]
  let seed : Order.PartialIso ℚ ℚ :=
    ⟨insert (a, b) (I.image (fun i => (i, i))), by
      intro p hp q hq
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp hq with rfl | hq
        · simp
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          simpa only [Prod.fst, Prod.snd, cmp_swap] using congrArg Ordering.swap (hcmp i hi)
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hcmp i hi
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
          rfl⟩
  obtain ⟨e, he⟩ := extend_partialIso seed
  refine ⟨e, he _ _ (Finset.mem_insert_self _ _), ?_⟩
  intro i hi
  exact he i i (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi))

end LargeIndependentSets

end OAI
