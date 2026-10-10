import OAI.Analysis.LipschitzHilbert.Estimates.DisjointIntervalVariation

namespace OAI

/-! Disjoint intervals fit into a partition of the original finite
horizon. Each interval is collapsed to one jump at its right endpoint;
the gaps contribute additional nonnegative variation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private def intervalCollapse (a b k : ℕ) : ℕ :=
  if k < b then min k a else k

private theorem intervalCollapse_mono (a b : ℕ) : Monotone (intervalCollapse a b) := by
  intro k l hkl
  unfold intervalCollapse
  split_ifs with hk hl
  · exact min_le_min hkl le_rfl
  · exact (min_le_left _ _).trans hkl
  · omega
  · exact hkl

private def disjointCollapse {ι : Type*} [Fintype ι] (a b : ι → ℕ) (k : ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun q : Option ι => q.elim k (fun i => intervalCollapse (a i) (b i) k))

private theorem disjointCollapse_mono {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    Monotone (disjointCollapse a b) := by
  intro k l hkl
  apply Finset.le_inf'
  intro q _
  have h := Finset.inf'_le
    (fun q : Option ι => q.elim k (fun i => intervalCollapse (a i) (b i) k))
    (Finset.mem_univ q)
  apply h.trans
  cases q with
  | none => exact hkl
  | some i => exact intervalCollapse_mono (a i) (b i) hkl

private theorem disjointCollapse_le {ι : Type*} [Fintype ι] (a b : ι → ℕ) (k : ℕ) :
    disjointCollapse a b k ≤ k :=
  Finset.inf'_le_of_le (f := fun q : Option ι =>
    q.elim k (fun i => intervalCollapse (a i) (b i) k))
    (Finset.mem_univ none) le_rfl

private theorem disjointCollapse_endpoints {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (hab : ∀ i, a i < b i)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) (i : ι) :
    disjointCollapse a b (b i) = b i ∧
      disjointCollapse a b (b i-1) = a i := by
  constructor
  · apply le_antisymm (disjointCollapse_le a b _)
    apply Finset.le_inf'
    intro q _
    cases q with
    | none => exact le_rfl
    | some j =>
      dsimp only [Option.elim_some]
      by_cases hij : i = j
      · subst j
        simp [intervalCollapse]
      · rcases hdisjoint i j hij with h | h
        · have hi : b i ≤ a j := h
          unfold intervalCollapse
          split_ifs <;> omega
        · have hj := hab i
          have hbji : b j ≤ b i := h.trans hj.le
          simp [intervalCollapse,not_lt.mpr hbji]
  · apply le_antisymm
    · have heq : intervalCollapse (a i) (b i) (b i-1) = a i := by
        have hi := hab i
        unfold intervalCollapse
        rw [ite_eq_left (by omega),min_eq_right (by omega)]
      exact (Finset.inf'_le
        (fun q : Option ι => q.elim (b i-1) (fun j => intervalCollapse (a j) (b j) (b i-1)))
        (Finset.mem_univ (some i))).trans_eq heq
    · apply Finset.le_inf'
      intro q _
      have hi := hab i
      cases q with
      | none => dsimp only [Option.elim_none]; omega
      | some j =>
        dsimp only [Option.elim_some]
        by_cases hij : i = j
        · subst j
          unfold intervalCollapse
          split_ifs <;> omega
        · rcases hdisjoint i j hij with h | h
          · unfold intervalCollapse
            split_ifs <;> omega
          · have hbji : b j ≤ b i-1 := by omega
            simp only [intervalCollapse,not_lt.mpr hbji,ite_false]
            omega

/-- No padding or multiplicative loss is needed for disjoint intervals
inside the original finite horizon. -/
theorem disjoint_increment_cube_sum_exact {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖F (b i)-F (a i)‖^3) ≤ finiteCubicVariation F N := by
  classical
  let p : Fin (N+1) → Fin (N+1) := fun k =>
    ⟨disjointCollapse a b k.val, (disjointCollapse_le a b k.val).trans_lt k.isLt⟩
  have hp : Monotone p := fun _ _ h => disjointCollapse_mono a b h
  let e : ι → Fin N := fun i => ⟨b i-1, by have := hab i; have := hb i; omega⟩
  have he : Function.Injective e := by
    intro i j hij
    have heq := congrArg Fin.val hij
    dsimp only [e] at heq
    by_contra hne
    have hi := hab i
    have hj := hab j
    rcases hdisjoint i j hne with h | h <;> omega
  have hpa (i : ι) : (p (e i).castSucc).val = a i :=
    (disjointCollapse_endpoints a b hab hdisjoint i).2
  have hpb (i : ι) : (p (e i).succ).val = b i := by
    have hi := hab i
    change disjointCollapse a b (b i-1+1) = b i
    rw [Nat.sub_add_cancel (by omega)]
    exact (disjointCollapse_endpoints a b hab hdisjoint i).1
  have hselect : (∑ i, ‖F (b i)-F (a i)‖^3) ≤
      ∑ j : Fin N, ‖F (p j.succ)-F (p j.castSucc)‖^3 := by
    refine Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
      e (fun i _ j _ h => he h) (Finset.subset_univ _) ?_ ?_
    · intro i _
      rw [hpa,hpb]
    · intro j _ _
      positivity
  exact hselect.trans (partition_le_finiteCubicVariation F N p hp)

end LipschitzHilbert

end

end OAI
