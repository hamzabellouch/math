import OAI.Probability.MatroidProphet.AdaptiveResampling

namespace OAI

namespace MatroidProphet
open Finset
variable {α β γ : Type*} [DecidableEq α]

def RevealTree.map (f : β → γ) : RevealTree α β → RevealTree α γ
  | .leaf b => .leaf (f b)
  | .query e no yes => .query e (no.map f) (yes.map f)

lemma RevealTree.fresh_map (tree : RevealTree α β) (f : β → γ) (V : Finset α) :
    (tree.map f).Fresh V ↔ tree.Fresh V := by
  induction tree generalizing V with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [map, Fresh, ihn, ihy]

lemma RevealTree.run_map (tree : RevealTree α β) (f : β → γ) (S : Finset α) :
    (tree.map f).run S = f (tree.run S) := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, run]
    split_ifs <;> simp_all

def revealBatch : List α → (Finset α → RevealTree α β) → RevealTree α β
  | [], cont => cont ∅
  | e :: xs, cont => .query e (revealBatch xs cont)
      (revealBatch xs (fun I => cont (insert e I)))

lemma erase_sdiff_eq_sdiff_insert (S X : Finset α) (e : α) :
    S.erase e \ X = S \ insert e X := by
  ext x
  simp only [mem_sdiff, mem_erase, mem_insert]
  tauto

lemma revealBatch_fresh (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (V : Finset α)
    (hXV : xs.toFinset ⊆ V)
    (hcont : ∀ I ⊆ xs.toFinset, (cont I).Fresh (V \ xs.toFinset)) :
    (revealBatch xs cont).Fresh V := by
  induction xs generalizing cont V with
  | nil => simpa [revealBatch] using hcont ∅ (empty_subset _)
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have heV : e ∈ V := hXV (by simp)
    have hsub : xs.toFinset ⊆ V.erase e := by
      intro x hx
      refine mem_erase.mpr ⟨?_, hXV (by simp [hx])⟩
      intro h; subst x; exact heX hx
    have htail := (List.nodup_cons.mp hxs).2
    refine ⟨heV, ih htail cont (V.erase e) hsub ?_,
      ih htail (fun I => cont (insert e I)) (V.erase e) hsub ?_⟩
    · intro I hI
      rw [erase_sdiff_eq_sdiff_insert]
      simpa only [List.toFinset_cons] using hcont I (by simpa using hI.trans (subset_insert e xs.toFinset))
    · intro I hI
      rw [erase_sdiff_eq_sdiff_insert]
      simpa only [List.toFinset_cons] using hcont (insert e I) (by simpa using insert_subset_insert e hI)

lemma revealBatch_run (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (S : Finset α) :
    (revealBatch xs cont).run S = (cont (S ∩ xs.toFinset)).run (S \ xs.toFinset) := by
  induction xs generalizing cont S with
  | nil => simp [revealBatch]
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have htail := (List.nodup_cons.mp hxs).2
    have hinter : S.erase e ∩ xs.toFinset = S ∩ xs.toFinset := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heX]
      · simp [hx]
    by_cases heS : e ∈ S
    · rw [revealBatch, RevealTree.run, ite_eq_left heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : insert e (S ∩ xs.toFinset) = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins]
    · rw [revealBatch, RevealTree.run, ite_eq_right heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : S ∩ xs.toFinset = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins]

lemma revealBatch_queried (xs : List α) (hxs : xs.Nodup)
    (cont : Finset α → RevealTree α β) (S : Finset α) :
    (revealBatch xs cont).queried S =
      xs.toFinset ∪ (cont (S ∩ xs.toFinset)).queried (S \ xs.toFinset) := by
  induction xs generalizing cont S with
  | nil => simp [revealBatch]
  | cons e xs ih =>
    have heX : e ∉ xs.toFinset := by simpa using (List.nodup_cons.mp hxs).1
    have htail := (List.nodup_cons.mp hxs).2
    have hinter : S.erase e ∩ xs.toFinset = S ∩ xs.toFinset := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heX]
      · simp [hx]
    by_cases heS : e ∈ S
    · rw [revealBatch, RevealTree.queried, ite_eq_left heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : insert e (S ∩ xs.toFinset) = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins, insert_union]
    · rw [revealBatch, RevealTree.queried, ite_eq_right heS, ih htail,
        hinter, erase_sdiff_eq_sdiff_insert]
      have hins : S ∩ xs.toFinset = S ∩ insert e xs.toFinset := by
        ext x
        by_cases hx : x = e
        · subst x; simp [heS]
        · simp [hx]
      simp only [List.toFinset_cons, hins, insert_union]

lemma RevealTree.queried_map (tree : RevealTree α β) (f : β → γ) (S : Finset α) :
    (tree.map f).queried S = tree.queried S := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, queried]
    split_ifs <;> simp_all

lemma RevealTree.hybrid_map (tree : RevealTree α β) (f : β → γ) (S T : Finset α) :
    (tree.map f).hybrid S T = tree.hybrid S T := by
  induction tree generalizing S T with
  | leaf b => rfl
  | query e no yes ihn ihy =>
    simp only [map, hybrid, ihn, ihy]

structure RevealRecord (α β : Type*) where
  value : β
  queried : Finset α
  positive : Finset α

def RevealTree.record : RevealTree α β → RevealTree α (RevealRecord α β)
  | .leaf b => .leaf ⟨b, ∅, ∅⟩
  | .query e no yes => .query e
      (no.record.map (fun r => ⟨r.value, insert e r.queried, r.positive⟩))
      (yes.record.map (fun r => ⟨r.value, insert e r.queried, insert e r.positive⟩))

lemma RevealTree.record_fresh (tree : RevealTree α β) (V : Finset α) :
    tree.record.Fresh V ↔ tree.Fresh V := by
  induction tree generalizing V with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, Fresh, fresh_map, ihn, ihy]

lemma RevealTree.record_run (tree : RevealTree α β) (S : Finset α) :
    tree.record.run S = ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ := by
  induction tree generalizing S with
  | leaf b => simp [record, run, queried]
  | query e no yes ihn ihy =>
    by_cases heS : e ∈ S
    · simp only [record, run, queried, ite_eq_left heS, run_map, ihy]
      congr 1
      ext x
      by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]
    · simp only [record, run, queried, ite_eq_right heS, run_map, ihn]
      congr 1
      ext x
      by_cases hxe : x = e
      · subst x; simp [heS]
      · simp [hxe]

lemma RevealTree.record_hybrid (tree : RevealTree α β) (S T : Finset α) :
    tree.record.hybrid S T = tree.hybrid S T := by
  induction tree generalizing S T with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, hybrid, hybrid_map, ihn, ihy]

lemma RevealTree.transcript_hybrid_independent (tree : RevealTree α β)
    (q : α → ℝ) (V : Finset α) (fresh : tree.Fresh V)
    (φ : RevealRecord α β → ℝ) (ψ : Finset α → ℝ) :
    bitsExpectation q V (fun S => bitsExpectation q V (fun T =>
      φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (tree.hybrid S T))) =
      bitsExpectation q V (fun S => φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩) *
        bitsExpectation q V ψ := by
  have h := tree.record.hybrid_independent q V ((tree.record_fresh V).mpr fresh) φ ψ
  simpa only [record_run, record_hybrid] using h

lemma RevealTree.transcript_freshness (tree : RevealTree α β)
    (q : α → ℝ) (V Q : Finset α) (fresh : tree.Fresh V)
    (φ : RevealRecord α β → ℝ) (ψ : Finset α → ℝ)
    (support : ∀ r, r.queried ≠ Q → φ r = 0) :
    bitsExpectation q V (fun S =>
      φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (S \ Q)) =
      bitsExpectation q V (fun S => φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩) *
        bitsExpectation q V (fun S => ψ (S \ Q)) := by
  have h := tree.transcript_hybrid_independent q V fresh φ (fun S => ψ (S \ Q))
  rw [← h]
  apply bitsExpectation_congr
  intro S hS
  by_cases hQ : tree.queried S = Q
  · have hhybrid (T : Finset α) (hT : T ⊆ V) : tree.hybrid S T \ Q = S \ Q := by
      rw [tree.hybrid_eq_resample V S T fresh hS hT, hQ]
      ext e
      simp only [mem_sdiff, mem_union, mem_inter]
      tauto
    have hc : bitsExpectation q V (fun T =>
        φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (tree.hybrid S T \ Q)) =
        bitsExpectation q V (fun _ =>
          φ ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ * ψ (S \ Q)) := by
      apply bitsExpectation_congr
      intro T hT
      rw [hhybrid T hT]
    rw [hc, bitsExpectation_const]
  · have hf := support ⟨tree.run S, tree.queried S, S ∩ tree.queried S⟩ hQ
    simp only [hf, zero_mul, bitsExpectation_const]

lemma RevealTree.record_queried (tree : RevealTree α β) (S : Finset α) :
    tree.record.queried S = tree.queried S := by
  induction tree generalizing S with
  | leaf b => rfl
  | query e no yes ihn ihy => simp only [record, queried, queried_map, ihn, ihy]

end MatroidProphet

end OAI
