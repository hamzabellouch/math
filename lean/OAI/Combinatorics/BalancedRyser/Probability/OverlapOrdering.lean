import Mathlib

namespace OAI

namespace Balanced.OverlapOrdering

variable {α : Type*} [DecidableEq α]

theorem exists_pair_partition (G : SimpleGraph α) (I : Finset α) :
    ∃ R S U : Finset α,
      R ∪ S ∪ U = I ∧ Disjoint R S ∧ Disjoint R U ∧ Disjoint S U ∧
      R.card = S.card ∧
      (∀ v ∈ S, ∃ u ∈ R, G.Adj u v) ∧
      (∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v) := by
  classical
  refine Finset.strongInductionOn I ?_
  intro I ih
  by_cases he : ∃ a ∈ I, ∃ b ∈ I, G.Adj a b
  · obtain ⟨a, ha, b, hb, habG⟩ := he
    have hab : a ≠ b := habG.ne
    let J := (I.erase a).erase b
    have hJI : J ⊂ I := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(Finset.erase_subset b (I.erase a)).trans (Finset.erase_subset a I), ?_⟩
      intro h
      have : a ∈ J := h.symm ▸ ha
      simp [J] at this
    obtain ⟨R, S, U, hcover, hRS, hRU, hSU, hcard, hpartners, hind⟩ := ih J hJI
    have hRsub : R ⊆ J := by
      rw [← hcover]
      exact (Finset.subset_union_left).trans Finset.subset_union_left
    have hSsub : S ⊆ J := by
      rw [← hcover]
      exact (Finset.subset_union_right).trans Finset.subset_union_left
    have hUsub : U ⊆ J := by
      rw [← hcover]
      exact Finset.subset_union_right
    have haR : a ∉ R := by intro h; have := hRsub h; simp [J] at this
    have haS : a ∉ S := by intro h; have := hSsub h; simp [J] at this
    have haU : a ∉ U := by intro h; have := hUsub h; simp [J] at this
    have hbR : b ∉ R := by intro h; have := hRsub h; simp [J] at this
    have hbS : b ∉ S := by intro h; have := hSsub h; simp [J] at this
    have hbU : b ∉ U := by intro h; have := hUsub h; simp [J] at this
    refine ⟨insert a R, insert b S, U, ?_, ?_, ?_, ?_, ?_, ?_, hind⟩
    · ext x
      have hx := Finset.ext_iff.mp hcover x
      simp only [Finset.mem_union, Finset.mem_insert] at hx ⊢
      simp only [J, Finset.mem_erase] at hx
      grind
    · simp [Finset.disjoint_insert_left, Finset.disjoint_insert_right,
        hab.symm, hbR, haS, hRS]
    · simp [Finset.disjoint_insert_left, haU, hRU]
    · simp [Finset.disjoint_insert_left, hbU, hSU]
    · simp [Finset.card_insert_of_notMem haR, Finset.card_insert_of_notMem hbS, hcard]
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨a, Finset.mem_insert_self _ _, habG⟩
      · obtain ⟨u, hu, huv⟩ := hpartners v hv
        exact ⟨u, Finset.mem_insert_of_mem hu, huv⟩
  · refine ⟨∅, ∅, I, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro u hu v hv huv
    exact he ⟨u, hu, v, hv, huv⟩

theorem exists_three_level_ranking (G : SimpleGraph α) (I : Finset α)
    (hneighbour : ∀ v ∈ I, ∃ u ∈ I, G.Adj u v) :
    ∃ R ⊆ I, ∃ h : α → ℕ,
      2 * R.card ≤ I.card ∧ (∀ v, h v ≤ 2) ∧
      (∀ v ∈ I, v ∉ R → ∃ u ∈ I, G.Adj u v ∧ h u < h v) := by
  classical
  obtain ⟨R, S, U, hcover, hRS, hRU, hSU, hcard, hpartners, hind⟩ :=
    exists_pair_partition G I
  have hRsub : R ⊆ I := by
    rw [← hcover]
    exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hSsub : S ⊆ I := by
    rw [← hcover]
    exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hcardbound : 2 * R.card ≤ I.card := by
    have h := Finset.card_le_card (Finset.union_subset hRsub hSsub)
    rw [Finset.card_union_of_disjoint hRS, ← hcard] at h
    omega
  let height : α → ℕ := fun v => if v ∈ R then 0 else if v ∈ S then 1 else 2
  refine ⟨R, hRsub, height, hcardbound, ?_, ?_⟩
  · intro v
    dsimp [height]
    split_ifs <;> omega
  · intro v hv hvR
    by_cases hvS : v ∈ S
    · obtain ⟨u, hu, huv⟩ := hpartners v hvS
      exact ⟨u, hRsub hu, huv, by simp [height, hu, hvR, hvS]⟩
    · have hvU : v ∈ U := by
        rw [← hcover] at hv
        simpa [hvR, hvS] using hv
      obtain ⟨u, hu, huv⟩ := hneighbour v hv
      have huU : u ∉ U := fun huU => hind u huU v hvU huv
      have huRS : u ∈ R ∨ u ∈ S := by
        rw [← hcover] at hu
        simpa [huU] using hu
      refine ⟨u, hu, huv, ?_⟩
      rcases huRS with huR | huS
      · simp [height, huR, hvR, hvS]
      · by_cases huR : u ∈ R <;> simp [height, huR, huS, hvR, hvS]

theorem exists_sorted_permutation {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) :
    ∃ π : Equiv.Perm (Fin n), StrictMono (f ∘ π) := by
  classical
  let S := Finset.univ.image f
  have hcard : S.card = n := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  let g : Fin n → S := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      exact hf (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp x.property
      refine ⟨i, ?_⟩
      apply Subtype.ext
      exact hix
  let e : Fin n ≃ S := Equiv.ofBijective g hg
  let o : Fin n ≃o S := S.orderIsoOfFin hcard
  let π : Equiv.Perm (Fin n) := o.toEquiv.trans e.symm
  have hkey : ∀ i, f (π i) = (o i).val := by
    intro i
    exact congrArg Subtype.val (e.apply_symm_apply (o i))
  refine ⟨π, ?_⟩
  intro i j hij
  change f (π i) < f (π j)
  rw [hkey, hkey]
  exact o.strictMono hij

theorem exists_permutation_with_few_roots {n : ℕ} (G : SimpleGraph (Fin n))
    (hneighbour : ∀ v, ∃ u, G.Adj u v) :
    ∃ π : Equiv.Perm (Fin n), ∃ R : Finset (Fin n),
      2 * R.card ≤ n ∧
      ∀ i, i ∉ R → ∃ j, j < i ∧ G.Adj (π j) (π i) := by
  classical
  obtain ⟨R, hR, height, hcard, hheight, hprev⟩ :=
    exists_three_level_ranking G Finset.univ (by
      intro v hv
      obtain ⟨u, huv⟩ := hneighbour v
      exact ⟨u, Finset.mem_univ u, huv⟩)
  let rank : Fin n → ℕ := fun v => height v * n + v.val
  have hrank : Function.Injective rank := by
    intro u v huv
    apply Fin.ext
    have he := congrArg (fun z => z % n) huv
    simpa [rank, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt u.isLt,
      Nat.mod_eq_of_lt v.isLt] using he
  have hlt : ∀ u v, height u < height v → rank u < rank v := by
    intro u v huv
    dsimp [rank]
    calc
      height u * n + u.val < (height u + 1) * n := by nlinarith [u.isLt]
      _ ≤ height v * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt huv)
      _ ≤ height v * n + v.val := Nat.le_add_right _ _
  obtain ⟨π, hπ⟩ := exists_sorted_permutation rank hrank
  refine ⟨π, R.image π.symm, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ π.symm.injective]
    simpa using hcard
  · intro i hi
    have hiR : π i ∉ R := by
      intro h
      apply hi
      exact Finset.mem_image.mpr ⟨π i, h, π.symm_apply_apply i⟩
    obtain ⟨u, hu, huadj, huh⟩ := hprev (π i) (Finset.mem_univ _) hiR
    refine ⟨π.symm u, ?_, by simpa using huadj⟩
    apply hπ.lt_iff_lt.mp
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hlt u (π i) huh

theorem exists_even_permutation_with_few_roots {s : ℕ}
    (G : SimpleGraph (Fin (2 * s))) (hneighbour : ∀ v, ∃ u, G.Adj u v) :
    ∃ π : Equiv.Perm (Fin (2 * s)), ∃ R : Finset (Fin (2 * s)),
      R.card ≤ s ∧
      ∀ i, i ∉ R → ∃ j, j < i ∧ G.Adj (π j) (π i) := by
  obtain ⟨π, R, hcard, hprev⟩ := exists_permutation_with_few_roots G hneighbour
  exact ⟨π, R, by omega, hprev⟩

theorem exists_pattern_ordering {γ : Type*} [DecidableEq γ] {s : ℕ}
    (C : Fin (2 * s) → Finset γ) (K₀ : Finset γ)
    (hnoiso : ∀ i, ∃ j, j ≠ i ∧ ((C j \ K₀) ∩ (C i \ K₀)).Nonempty) :
    ∃ π : Equiv.Perm (Fin (2 * s)), ∃ R : Finset (Fin (2 * s)),
      R.card ≤ s ∧ ∀ i, i ∉ R →
        ∃ j, j < i ∧ ((C (π j) \ K₀) ∩ (C (π i) \ K₀)).Nonempty := by
  let G : SimpleGraph (Fin (2 * s)) := {
    Adj := fun i j => i ≠ j ∧ ((C i \ K₀) ∩ (C j \ K₀)).Nonempty
    symm := by
      constructor
      intro i j hij
      exact ⟨hij.1.symm, by simpa only [Finset.inter_comm] using hij.2⟩
    loopless := by
      constructor
      intro i hii
      exact hii.1 rfl }
  have hG : ∀ v, ∃ u, G.Adj u v := by
    intro v
    obtain ⟨u, huv, hC⟩ := hnoiso v
    exact ⟨u, huv, hC⟩
  obtain ⟨π, R, hcard, hprev⟩ := exists_even_permutation_with_few_roots G hG
  refine ⟨π, R, hcard, ?_⟩
  intro i hi
  obtain ⟨j, hji, hGji⟩ := hprev i hi
  exact ⟨j, hji, hGji.2⟩

end Balanced.OverlapOrdering

end OAI
