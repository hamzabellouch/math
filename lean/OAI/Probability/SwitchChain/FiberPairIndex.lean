import OAI.Probability.SwitchChain.PairFiber
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.FiberPairIndex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_disjoint_pairs_eq_sum_supported
    (a s : Finset V) (F : Finset V → ℝ) (has : Disjoint a s)
    (hzero : ∀ b, b.card = 2 → ¬ b ⊆ s → F b = 0) :
    (∑ b ∈ Finset.univ.powersetCard 2, if Disjoint a b then F b else 0) =
      ∑ b ∈ s.powersetCard 2, F b := by
  classical
  have hsub : s.powersetCard 2 ⊆ Finset.univ.powersetCard 2 := by
    intro b hb
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hb).2⟩
  calc
    _ = ∑ b ∈ Finset.univ.powersetCard 2, F b := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbs : b ⊆ s
      · rw [ite_eq_left (has.mono_right hbs)]
      · rw [hzero b (Finset.mem_powersetCard.mp hb).2 hbs]
        split <;> rfl
    _ = ∑ b ∈ s.powersetCard 2, F b := by
      symm
      apply Finset.sum_subset hsub
      intro b hb hnot
      apply hzero b (Finset.mem_powersetCard.mp hb).2
      intro hbs
      exact hnot (Finset.mem_powersetCard.mpr
        ⟨hbs, (Finset.mem_powersetCard.mp hb).2⟩)

theorem singletonSet_disjoint (G : SimpleGraph V) (i j : V) :
    Disjoint ({i,j} : Finset V) (PairFiber.singletonSet G i j) := by
  rw [Finset.disjoint_left]
  intro w hw hs
  have ho := (PairFiber.mem_singletonSet G i j w).mp hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact ho.1.1 rfl
  · exact ho.1.2 rfl

theorem sum_graph_pairs_eq_singleton_pairs {n : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n) (F : Finset (Fin n) → ℝ)
    (hzero : ∀ b, b.card = 2 →
      ¬ b ⊆ PairFiber.singletonSet G i j → F b = 0) :
    (∑ b ∈ PairResampling.pairs n,
      if Disjoint ({i,j} : Finset (Fin n)) b then F b else 0) =
      ∑ b ∈ (PairFiber.singletonSet G i j).powersetCard 2, F b := by
  exact sum_disjoint_pairs_eq_sum_supported {i,j} _ F
    (singletonSet_disjoint G i j) hzero

omit [Fintype V] [DecidableEq V] in

theorem sum_powersetCard_eq_subtype (s : Finset V) (k : ℕ)
    (F : Finset V → ℝ) :
    (∑ b ∈ s.powersetCard k, F b) =
      ∑ b ∈ (Finset.univ : Finset s).powersetCard k,
        F (b.map (Function.Embedding.subtype (fun x => x ∈ s))) := by
  have hu : (Finset.univ : Finset s).map
      (Function.Embedding.subtype (fun x => x ∈ s)) = s := by
    simpa only [Finset.univ_eq_attach] using (Finset.attach_map_val (s := s))
  conv_lhs => rw [← hu, Finset.powersetCard_map, Finset.sum_map]
  rfl

omit [Fintype V] in

theorem sum_pairs_insert (s : Finset V) (x : V) (hx : x ∉ s)
    (F : Finset V → ℝ) :
    (∑ b ∈ (insert x s).powersetCard 2, F b) =
      (∑ b ∈ s.powersetCard 2, F b) + ∑ y ∈ s, F {x,y} := by
  have hd : Disjoint (s.powersetCard 2)
      ((s.powersetCard 1).image (insert x)) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    rcases Finset.mem_image.mp hc with ⟨c, hc, rfl⟩
    exact hx ((Finset.mem_powersetCard.mp hb).1 (Finset.mem_insert_self _ _))
  have hi : Set.InjOn (insert x) (s.powersetCard 1 : Set (Finset V)) := by
    intro b hb c hc heq
    have hxb : x ∉ b := fun h => hx ((Finset.mem_powersetCard.mp hb).1 h)
    have hxc : x ∉ c := fun h => hx ((Finset.mem_powersetCard.mp hc).1 h)
    simpa [hxb, hxc] using congrArg (fun t : Finset V => t.erase x) heq
  rw [Finset.powersetCard_succ_insert hx 1, Finset.sum_union hd,
    Finset.sum_image hi, Finset.powersetCard_one, Finset.sum_map]
  rfl

omit [Fintype V] in

theorem twice_sum_pairs_eq_ordered (s : Finset V) (F : Finset V → ℝ) :
    2 * (∑ b ∈ s.powersetCard 2, F b) =
      ∑ x ∈ s, ∑ y ∈ s, if x = y then 0 else F {x,y} := by
  induction s using Finset.induction_on with
  | empty =>
      have he : (∅ : Finset V).powersetCard 2 = ∅ :=
        Finset.powersetCard_eq_empty.mpr (by simp)
      simp [he]
  | @insert x s hx ih =>
      rw [sum_pairs_insert s x hx F, Finset.sum_insert hx]
      simp_rw [Finset.sum_insert hx]
      have hxy : (∑ y ∈ s, if x = y then 0 else F {x,y}) =
          ∑ y ∈ s, F {x,y} := by
        apply Finset.sum_congr rfl
        intro y hy
        have hne : x ≠ y := fun h => hx (h.symm ▸ hy)
        rw [ite_eq_right hne]
      have hyx : (∑ y ∈ s, if y = x then 0 else F {y,x}) =
          ∑ y ∈ s, F {x,y} := by
        apply Finset.sum_congr rfl
        intro y hy
        have hne : y ≠ x := fun h => hx (h ▸ hy)
        rw [ite_eq_right hne, Finset.pair_comm]
      simp only [ite_true, zero_add, Finset.sum_add_distrib]
      rw [hxy, hyx, ← ih]
      ring

omit [Fintype V] in

theorem sum_pairs_eq_half_ordered (s : Finset V) (F : Finset V → ℝ) :
    (∑ b ∈ s.powersetCard 2, F b) =
      (1 / 2 : ℝ) * ∑ x ∈ s, ∑ y ∈ s, if x = y then 0 else F {x,y} := by
  rw [← twice_sum_pairs_eq_ordered s F]
  ring

omit [Fintype V] in

theorem sum_pairs_eq_half_subtype (s : Finset V) (F : Finset V → ℝ) :
    (∑ b ∈ s.powersetCard 2, F b) =
      (1 / 2 : ℝ) * ∑ x : s, ∑ y : s,
        if x = y then 0 else F {x.val,y.val} := by
  rw [sum_pairs_eq_half_ordered]
  congr 1
  simp only [Subtype.ext_iff]
  calc
    _ = ∑ x : s, ∑ y ∈ s, if x.val = y then 0 else F {x.val,y} :=
      (Finset.sum_coe_sort s (fun x => ∑ y ∈ s, if x = y then 0 else F {x,y})).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Finset.sum_coe_sort s (fun y => if x.val = y then 0 else F {x.val,y})).symm

theorem sum_graph_pairs_eq_half_singleton_ordered {n : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n) (F : Finset (Fin n) → ℝ)
    (hzero : ∀ b, b.card = 2 →
      ¬ b ⊆ PairFiber.singletonSet G i j → F b = 0) :
    (∑ b ∈ PairResampling.pairs n,
      if Disjoint ({i,j} : Finset (Fin n)) b then F b else 0) =
      (1 / 2 : ℝ) * ∑ x : PairFiber.singletonSet G i j,
        ∑ y : PairFiber.singletonSet G i j,
          if x = y then 0 else F {x.val,y.val} := by
  rw [sum_graph_pairs_eq_singleton_pairs G i j F hzero]
  exact sum_pairs_eq_half_subtype _ F

end Problem315.FiberPairIndex

end

end OAI
