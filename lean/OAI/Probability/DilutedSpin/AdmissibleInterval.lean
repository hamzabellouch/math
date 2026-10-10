import OAI.Probability.DilutedSpin.VertexContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance admissibleIntervalPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

/-- With every other depth fixed, admissible values of one branching
coordinate form an interval. No spacing or regularity is needed here. -/
lemma admissible_update_between (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    {a b t lo hi : ℕ} (hat : a≤t) (htb : t≤b)
    (ha : Admissible S (updateCoordinate q v a) lo hi)
    (hb : Admissible S (updateCoordinate q v b) lo hi) :
    Admissible S (updateCoordinate q v t) lo hi := by
  induction S generalizing lo hi with
  | leaf => exact v.elim
  | node k hk C ih =>
    cases v with
    | none =>
      simp only [update_root (hk := hk),Admissible,rootSchedule] at ha hb ⊢
      exact ⟨ha.1.trans hat,htb.trans_lt hb.2.1,
        fun i => admissible_mono_lower (C i) _ (Nat.succ_le_succ htb) (hb.2.2 i)⟩
    | some a =>
      obtain ⟨i,v⟩ := a
      constructor
      · simpa only [update_desc_root (hk := hk)] using ha.1
      constructor
      · simpa only [update_desc_root (hk := hk)] using ha.2.1
      intro j
      by_cases hj : j=i
      · subst j
        have haa := ha.2.2 i
        have hbb := hb.2.2 i
        simp only [update_desc_root (hk := hk),update_desc_same (hk := hk)] at haa hbb ⊢
        exact ih i _ v haa hbb
      · have haa := ha.2.2 j
        simpa only [update_desc_root (hk := hk),update_desc_other q i v _ j hj] using haa

/-- Interval form of the literal one-vertex Dirichlet-energy estimate. -/
theorem scheduled_vertex_Ico_energy_le {Ω : Type} [Fintype Ω]
    (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    (a b : ℕ) (hab : a≤b)
    (ha : Admissible S (updateCoordinate q v a) d (d+H))
    (hb : Admissible S (updateCoordinate q v b) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t ∈ Finset.Ico a b,
      (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
       PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2) ≤
      (vertexArity S v:ℝ)^2 := by
  have he := scheduled_vertex_energy_le H d S q v a (b-a) (by
    intro t
    apply admissible_update_between S q v (Nat.le_add_right _ _) ?_ ha hb
    have ht := t.isLt
    omega) T f hf
  let E : ℕ → ℝ := fun t =>
    (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
     PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2
  have he' : (∑ t : Fin (b-a), E (a+t.val)) ≤ (vertexArity S v:ℝ)^2 := by
    simpa only [E,Fin.val_castSucc,Fin.val_succ,Nat.add_assoc] using he
  rw [Fin.sum_univ_eq_sum_range (fun t => E (a+t)) (b-a)] at he'
  change (∑ t ∈ Finset.Ico a b, E t) ≤ _
  rwa [Finset.sum_Ico_eq_sum_range]


/-- Restriction to ANY set of allowed one-step shifts cannot raise the
single-coordinate energy. The proof uses the actual admissible hull. -/
theorem scheduled_vertex_subset_energy_le {Ω : Type} [Fintype Ω]
    (H d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (v : S.Vertex)
    (I : Finset ℕ)
    (ha : ∀ t ∈ I, Admissible S (updateCoordinate q v t) d (d+H) ∧
      Admissible S (updateCoordinate q v (t+1)) d (d+H))
    (T : KernelTower Ω H) (f : FinitePath Ω H → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (∑ t ∈ I,
      (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
       PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2) ≤
      (vertexArity S v:ℝ)^2 := by
  classical
  by_cases hI : I.Nonempty
  · have hm := I.min'_mem hI
    have hM := I.max'_mem hI
    have hsub : I ⊆ Finset.Ico (I.min' hI) (I.max' hI+1) := by
      intro t ht
      exact Finset.mem_Ico.mpr ⟨I.min'_le t ht,Nat.lt_succ_of_le (I.le_max' t ht)⟩
    calc
      _ ≤ ∑ t ∈ Finset.Ico (I.min' hI) (I.max' hI+1),
          (PrescribedTree.treeMean (realize H d S (updateCoordinate q v t)) T f-
           PrescribedTree.treeMean (realize H d S (updateCoordinate q v (t+1))) T f)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := scheduled_vertex_Ico_energy_le H d S q v _ _
        ((I.min'_le _ hM).trans (Nat.le_succ _)) (ha _ hm).1 (ha _ hM).2 T f hf
  · have he : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [he,Finset.sum_empty]
    positivity

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
