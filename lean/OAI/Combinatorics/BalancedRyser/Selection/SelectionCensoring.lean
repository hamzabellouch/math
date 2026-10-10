import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcess

namespace OAI

namespace Balanced.Selection

noncomputable section
open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem card_le_filter_add_two (s : Finset V) (p r : V → Prop)
    [DecidablePred p] [DecidablePred r] :
    s.card ≤ (s.filter (fun v => ¬ p v ∧ ¬ r v)).card +
      (s.filter p).card + (s.filter r).card := by
  have hcover : s ⊆ s.filter (fun v => ¬ p v ∧ ¬ r v) ∪ s.filter p ∪ s.filter r := by
    intro v hv
    by_cases hp : p v
    · simp [hv, hp]
    · by_cases hr : r v <;> simp [hv, hp, hr]
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))

theorem card_le_filter_add_three (s : Finset V) (p r z : V → Prop)
    [DecidablePred p] [DecidablePred r] [DecidablePred z] :
    s.card ≤ (s.filter (fun v => ¬ p v ∧ ¬ r v ∧ ¬ z v)).card +
      (s.filter p).card + (s.filter r).card + (s.filter z).card := by
  have hcover : s ⊆ s.filter (fun v => ¬ p v ∧ ¬ r v ∧ ¬ z v) ∪
      s.filter p ∪ s.filter r ∪ s.filter z := by
    intro v hv
    by_cases hp : p v
    · simp [hv, hp]
    · by_cases hr : r v
      · simp [hv, hp, hr]
      · by_cases hz : z v <;> simp [hv, hp, hr, hz]
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))

end
end Balanced.Selection

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in
theorem mem_currentVertices_update_iff (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    v ∈ currentVertices G (update G S i w flags) ↔
      v ∈ currentVertices G S ∧ ¬ G.graph.Adj w v ∧
        flags v = false ∧ G.slot v ≠ i := by
  simp only [currentVertices, update, survivors, Finset.mem_filter,
    Finset.mem_erase]
  tauto

omit [Fintype I] [Fintype V] in

theorem currentVertices_update_subset (G : Input I V) (S : State I V)
    (i : I) (w : V) (flags : V → Bool) :
    currentVertices G (update G S i w flags) ⊆ currentVertices G S := by
  intro v hv
  exact (mem_currentVertices_update_iff G S i w v flags).mp hv |>.1

theorem exceptional_not_mem_currentVertices_update
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) {i : I} {w v : V} (flags : V → Bool)
    (hw : w ∈ domain G S i) (hex : w ∈ G.exceptional v) :
    v ∉ currentVertices G (update G S i w flags) := by
  intro hv
  obtain ⟨_, hconflict, _, hslot⟩ :=
    (mem_currentVertices_update_iff G S i w v flags).mp hv
  have hwi : G.slot w = i := (Finset.mem_filter.mp hw).2
  rcases hG.2.2.2.2.2.2.2 v w hex with hadj | heq
  · exact hconflict hadj.symm
  · exact hslot (heq.trans hwi)

omit [Fintype I] in
theorem postcheck_of_performedResult_some {q : ℕ} {G : Input I V}
    {S S' : State I V} {r : Noise I V}
    (h : performedResult q G S r = some S') :
    Postcheck q G S r.2.1 r.2.2 := by
  by_contra hn
  simp [performedResult, hn] at h

omit [Fintype I] in
theorem update_eq_of_performedResult_some {q : ℕ} {G : Input I V}
    {S S' : State I V} {r : Noise I V}
    (h : performedResult q G S r = some S') :
    update G S r.1 r.2.1 r.2.2 = S' := by
  simpa [performedResult, postcheck_of_performedResult_some h] using h

omit [Fintype I] in

theorem performedResult_none_of_domain_overflow {q : ℕ} {G : Input I V}
    {S : State I V} {r : Noise I V} {i : I} (hi : i ∈ S.remaining)
    (hlarge : (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ)) :
    performedResult q G S r = none := by
  have hn : ¬ Postcheck q G S r.2.1 r.2.2 := fun h =>
    (not_lt_of_ge (h.1 i hi)) hlarge
  simp [performedResult, hn]

omit [Fintype I] in
theorem performedResult_none_of_degree_overflow {q : ℕ} {G : Input I V}
    {S : State I V} {r : Noise I V} {v : V} (hv : v ∈ currentVertices G S)
    (hlarge : (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ)) :
    performedResult q G S r = none := by
  have hn : ¬ Postcheck q G S r.2.1 r.2.2 := fun h =>
    (not_lt_of_ge (h.2 v hv)) hlarge
  simp [performedResult, hn]

theorem relevant_successor_uncensored
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    {S S' : State I V} {r : Noise I V} {v : V}
    (hw : r.2.1 ∈ domain G S r.1)
    (hout : performedResult q G S r = some S')
    (hv : v ∈ currentVertices G S') :
    r.2.1 ∉ G.exceptional v ∧
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ) ≤
        (q : ℝ) ^ (1 / 8 : ℝ) := by
  have heq := update_eq_of_performedResult_some hout
  have hv' : v ∈ currentVertices G (update G S r.1 r.2.1 r.2.2) := heq ▸ hv
  refine ⟨fun hex => exceptional_not_mem_currentVertices_update hG S r.2.2 hw hex hv', ?_⟩
  exact (postcheck_of_performedResult_some hout).2 v
    (currentVertices_update_subset G S r.1 r.2.1 r.2.2 hv')

omit [Fintype I] in

theorem domain_loss_le_conflicts_add_thinning (G : Input I V) (S : State I V)
    {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    ((domain G S i).card : ℝ) -
      (((survivors G S w flags) ∩ domain G S i).card : ℝ) ≤
      (((neighbors G w) ∩ domain G S i).card : ℝ) +
        (((thinned G S w flags) ∩ domain G S i).card : ℝ) := by
  have hcover : domain G S i ⊆
      (survivors G S w flags ∩ domain G S i) ∪
      (neighbors G w ∩ domain G S i) ∪
      (thinned G S w flags ∩ domain G S i) := by
    intro u hu
    have hua : u ∈ S.alive := (Finset.mem_filter.mp hu).1
    have hui : G.slot u = i := (Finset.mem_filter.mp hu).2
    have huc : u ∈ currentVertices G S := by simp [currentVertices, hua, hui, hi]
    by_cases hadj : G.graph.Adj w u
    · simp [hu, neighbors, hadj]
    · cases hflag : flags u <;> simp [hu, survivors, thinned, huc, hadj, hflag]
  have hc := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hc' : ((domain G S i).card : ℝ) ≤
      (((survivors G S w flags) ∩ domain G S i).card : ℝ) +
      (((neighbors G w) ∩ domain G S i).card : ℝ) +
      (((thinned G S w flags) ∩ domain G S i).card : ℝ) := by
    exact_mod_cast hc
  linarith

theorem domain_loss_le_two_mul_rpow
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool)
    (hthin : (((thinned G S w flags) ∩ domain G S i).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)) :
    ((domain G S i).card : ℝ) -
      (((survivors G S w flags) ∩ domain G S i).card : ℝ) ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hsub : (neighbors G w) ∩ domain G S i ⊆
      (neighbors G w) ∩ slotVertices G i := by
    intro u hu
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hu).1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_inter.mp hu).2).2⟩⟩
  have hc : (((neighbors G w) ∩ domain G S i).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hG.2.2.2.2.1 w i)
  have hloss := domain_loss_le_conflicts_add_thinning G S hi w flags
  linarith

omit [Fintype I] in

theorem degree_loss_le_three_counts (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    (degree G S v : ℝ) - (degree G (update G S i w flags) v : ℝ) ≤
      (((neighbors G v) ∩ neighbors G w).card : ℝ) +
      (((thinned G S w flags) ∩ neighbors G v).card : ℝ) +
      (((neighbors G v) ∩ slotVertices G i).card : ℝ) := by
  have hcover : neighbors G v ∩ currentVertices G S ⊆
      (neighbors G v ∩ currentVertices G (update G S i w flags)) ∪
      (neighbors G v ∩ neighbors G w) ∪
      (thinned G S w flags ∩ neighbors G v) ∪
      (neighbors G v ∩ slotVertices G i) := by
    intro u hu
    obtain ⟨huv, huc⟩ := Finset.mem_inter.mp hu
    by_cases hadj : G.graph.Adj w u
    · have huw : u ∈ neighbors G w := by simp [neighbors, hadj]
      simp [huv, huw]
    · by_cases hslot : G.slot u = i
      · simp [huv, slotVertices, hslot]
      · cases hflag : flags u
        · have hun : u ∈ currentVertices G (update G S i w flags) :=
            (mem_currentVertices_update_iff G S i w u flags).mpr
              ⟨huc, hadj, hflag, hslot⟩
          simp [huv, hun]
        · have hut : u ∈ thinned G S w flags := by
            simp [thinned, huc, hadj, hflag]
          simp [huv, hut]
  have hc := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  have hc' : (degree G S v : ℝ) ≤
      (degree G (update G S i w flags) v : ℝ) +
      (((neighbors G v) ∩ neighbors G w).card : ℝ) +
      (((thinned G S w flags) ∩ neighbors G v).card : ℝ) +
      (((neighbors G v) ∩ slotVertices G i).card : ℝ) := by
    exact_mod_cast hc
  linarith

theorem degree_loss_le_three_mul_rpow
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) (i : I) (w v : V) (flags : V → Bool)
    (hex : w ∉ G.exceptional v)
    (hthin : (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)) :
    (degree G S v : ℝ) - (degree G (update G S i w flags) v : ℝ) ≤
      3 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hconflict := hG.2.2.2.2.2.2.1 v w hex
  have hslot := hG.2.2.2.2.1 v i
  have hloss := degree_loss_le_three_counts G S i w v flags
  linarith

omit [Fintype I] in

theorem degree_update_le (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    degree G (update G S i w flags) v ≤ degree G S v := by
  apply Finset.card_le_card
  exact Finset.inter_subset_inter_left (currentVertices_update_subset G S i w flags)

theorem abs_degree_update_sub_le_three_mul_rpow
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) (i : I) (w v : V) (flags : V → Bool)
    (hex : w ∉ G.exceptional v)
    (hthin : (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ)) :
    |(degree G (update G S i w flags) v : ℝ) - (degree G S v : ℝ)| ≤
      3 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  rw [abs_sub_comm, abs_of_nonneg
    (sub_nonneg.mpr (Nat.cast_le.mpr (degree_update_le G S i w v flags)))]
  exact degree_loss_le_three_mul_rpow hG S i w v flags hex hthin

omit [Fintype I] in

theorem currentVertices_subset_of_performed_steps
    {q T : ℕ} {G : Input I V} (S : ℕ → State I V) (r : ℕ → Noise I V)
    (hstep : ∀ k < T, performedResult q G (S k) (r k) = some (S (k + 1)))
    {s t : ℕ} (hst : s ≤ t) (ht : t ≤ T) :
    currentVertices G (S t) ⊆ currentVertices G (S s) := by
  induction t generalizing s with
  | zero =>
      have hs : s = 0 := Nat.eq_zero_of_le_zero hst
      subst s
      exact Finset.Subset.refl _
  | succ t ih =>
      by_cases heq : s = t + 1
      · subst s
        exact Finset.Subset.refl _
      · have hst' : s ≤ t := by omega
        have htt : t < T := by omega
        have heqS := update_eq_of_performedResult_some (hstep t htt)
        have hsub : currentVertices G (S (t + 1)) ⊆ currentVertices G (S t) := by
          rw [← heqS]
          exact currentVertices_update_subset G (S t) (r t).1 (r t).2.1 (r t).2.2
        exact hsub.trans (ih hst' (by omega))

theorem exceptional_not_relevant_later
    {G : Input I V} {q T : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : ℕ → State I V) (r : ℕ → Noise I V)
    (hstep : ∀ k < T, performedResult q G (S k) (r k) = some (S (k + 1)))
    {j t : ℕ} (hjt : j < t) (ht : t ≤ T) {v : V}
    (hw : (r j).2.1 ∈ domain G (S j) (r j).1)
    (hex : (r j).2.1 ∈ G.exceptional v) :
    v ∉ currentVertices G (S t) := by
  intro hv
  have hjT : j < T := lt_of_lt_of_le hjt ht
  have hvnext := currentVertices_subset_of_performed_steps S r hstep
    (Nat.succ_le_of_lt hjt) ht hv
  rw [← update_eq_of_performedResult_some (hstep j hjT)] at hvnext
  exact exceptional_not_mem_currentVertices_update hG (S j) (r j).2.2 hw hex hvnext

theorem relevant_final_uncensored_at
    {G : Input I V} {q T : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : ℕ → State I V) (r : ℕ → Noise I V)
    (hstep : ∀ k < T, performedResult q G (S k) (r k) = some (S (k + 1)))
    {j t : ℕ} (hjt : j < t) (ht : t ≤ T) {v : V}
    (hw : (r j).2.1 ∈ domain G (S j) (r j).1)
    (hv : v ∈ currentVertices G (S t)) :
    (r j).2.1 ∉ G.exceptional v ∧
      (((thinned G (S j) (r j).2.1 (r j).2.2) ∩ neighbors G v).card : ℝ) ≤
        (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hvnext := currentVertices_subset_of_performed_steps S r hstep
    (Nat.succ_le_of_lt hjt) ht hv
  exact relevant_successor_uncensored hG hw (hstep j (lt_of_lt_of_le hjt ht)) hvnext

omit [Fintype I] [Fintype V] in

theorem domain_update_eq_survivors_inter_domain (G : Input I V) (S : State I V)
    {i j : I} (hij : j ≠ i) (w : V) (flags : V → Bool) :
    domain G (update G S i w flags) j = survivors G S w flags ∩ domain G S j := by
  ext v
  simp only [domain, update, survivors, currentVertices, Finset.mem_filter,
    Finset.mem_inter]
  constructor
  · rintro ⟨⟨⟨⟨ha, hr⟩, hc, hf⟩, hne⟩, heq⟩
    exact ⟨⟨⟨ha, hr⟩, hc, hf⟩, ha, heq⟩
  · rintro ⟨⟨⟨ha, hr⟩, hc, hf⟩, _, heq⟩
    exact ⟨⟨⟨⟨ha, hr⟩, hc, hf⟩, fun h => hij (heq.symm.trans h)⟩, heq⟩

end
end Balanced.Selection.Process

end OAI
