import OAI.Probability.SwitchChain.PairFiber

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem315.PairFiber

theorem edgeBit_symm {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u v : V) : edgeBit G u v = edgeBit G v u := by
  unfold edgeBit
  congr 1
  exact propext (G.adj_comm u v)

theorem graphDegree_eq_sum_edgeBit {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    graphDegree G u = ∑ w, edgeBit G u w := by
  classical
  simp [graphDegree, edgeBit]

theorem degree_left_formula {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    graphDegree G i = edgeBit G i j + (commonSet G i j).card + (leftSet G i j).card := by
  classical
  have hp (w : Fin n) : edgeBit G i w =
      (if w = j then edgeBit G i j else 0) +
      (if w ∈ commonSet G i j then 1 else 0) +
      (if w ∈ leftSet G i j then 1 else 0) := by
    by_cases hwi : w = i
    · subst w
      simp [edgeBit, Outside, hij]
    by_cases hwj : w = j
    · subst w
      simp [edgeBit, Outside, Ne.symm hij]
    by_cases hiw : G.Adj i w <;> by_cases hjw : G.Adj j w <;>
      simp [edgeBit, Outside, hwi, hwj, hiw, hjw]
  rw [graphDegree_eq_sum_edgeBit]
  calc
    (∑ w, edgeBit G i w) = ∑ w, ((if w = j then edgeBit G i j else 0) +
      (if w ∈ commonSet G i j then 1 else 0) +
      (if w ∈ leftSet G i j then 1 else 0)) :=
        Finset.sum_congr rfl (fun w _ => hp w)
    _ = _ := by simp [Finset.sum_add_distrib, commonSet, leftSet]

theorem leftSet_card_eq_iff_degree_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H) :
    (leftSet G i j).card = (leftSet H i j).card ↔ graphDegree G i = graphDegree H i := by
  have hi : edgeBit G i j = edgeBit H i j := by
    unfold edgeBit
    congr 1
    exact propext (key_internal hk)
  have hc := commonSet_eq_of_key_eq hk
  rw [degree_left_formula G hij, degree_left_formula H hij, hi, hc]
  omega

theorem singleton_card_split {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    (singletonSet G i j).card = (leftSet G i j).card + (leftSet G j i).card := by
  classical
  have hu : singletonSet G i j = leftSet G i j ∪ leftSet G j i := by
    ext w
    simp only [mem_singletonSet, Finset.mem_union, mem_leftSet, Outside, Xor]
    tauto
  have hd : Disjoint (leftSet G i j) (leftSet G j i) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact ((mem_leftSet G i j w).mp hw).2.2 ((mem_leftSet G j i w).mp hw').2.1
  rw [hu, Finset.card_union_of_disjoint hd]

theorem degree_outside_formula {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hij : i ≠ j) (w : Fin n) :
    graphDegree G w = edgeBit G w i + edgeBit G w j +
      ∑ x ∈ Finset.univ.filter (Outside i j), edgeBit G w x := by
  classical
  have hp (x : Fin n) : edgeBit G w x =
      (if x = i then edgeBit G w i else 0) +
      (if x = j then edgeBit G w j else 0) +
      (if Outside i j x then edgeBit G w x else 0) := by
    by_cases hxi : x = i
    · subst x
      simp [Outside, hij]
    by_cases hxj : x = j
    · subst x
      simp [Outside, Ne.symm hij]
    simp [Outside, hxi, hxj]
  rw [graphDegree_eq_sum_edgeBit]
  calc
    (∑ x, edgeBit G w x) =
        ∑ x, ((if x = i then edgeBit G w i else 0) +
          (if x = j then edgeBit G w j else 0) +
          (if Outside i j x then edgeBit G w x else 0)) :=
      Finset.sum_congr rfl (fun x _ => hp x)
    _ = _ := by simp [Finset.sum_filter, Finset.sum_add_distrib]

theorem degree_outside_eq_of_key_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j w : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H)
    (hw : Outside i j w) : graphDegree G w = graphDegree H w := by
  classical
  have hc := key_count hk w
  have hc' : edgeBit G w i + edgeBit G w j = edgeBit H w i + edgeBit H w j := by
    simpa only [edgeBit_symm G i w, edgeBit_symm G j w,
      edgeBit_symm H i w, edgeBit_symm H j w] using hc
  rw [degree_outside_formula G hij w, degree_outside_formula H hij w, hc']
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hxo := (Finset.mem_filter.mp hx).2
  unfold edgeBit
  congr 1
  exact propext (key_outside hk hw hxo)

theorem degrees_eq_of_key_leftSet_card_eq {n : ℕ} {G H : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) (hk : key i j G = key i j H)
    (hl : (leftSet G i j).card = (leftSet H i j).card) :
    ∀ v, graphDegree G v = graphDegree H v := by
  have hi := (leftSet_card_eq_iff_degree_eq hij hk).mp hl
  have hs := congrArg Finset.card (singletonSet_eq_of_key_eq hk)
  have hr : (leftSet G j i).card = (leftSet H j i).card := by
    rw [singleton_card_split G i j, singleton_card_split H i j, hl] at hs
    omega
  have hks : key j i G = key j i H :=
    (key_swap G i j).symm.trans (hk.trans (key_swap H i j))
  have hj := (leftSet_card_eq_iff_degree_eq (Ne.symm hij) hks).mp hr
  intro v
  by_cases hvi : v = i
  · simpa [hvi] using hi
  by_cases hvj : v = j
  · simpa [hvj] using hj
  exact degree_outside_eq_of_key_eq hij hk ⟨hvi, hvj⟩

end Problem315.PairFiber

end

end OAI
