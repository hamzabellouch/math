import Mathlib

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section

theorem ordered_window_drop_sum {n : ℕ} (e l : Fin n→ℝ) (lo hi c : ℝ)
    (hc : 0≤c) (hlohi : lo≤hi) (he : ∀i,e i≤hi) (hl : ∀i,lo≤l i)
    (hw : ∀i,l i≤e i+c) (ho : ∀i j,i<j→e j≤l i+c) :
    (∑i,max 0 (e i-l i))≤hi-lo+2*(n:ℝ)*c := by
  induction n generalizing lo hi with
  | zero => simpa using sub_nonneg.mpr hlohi
  | succ n ih =>
    have hh:=ih (fun i=>e i.succ) (fun i=>l i.succ) lo (l 0+c)
      (by linarith [hl 0])
      (fun i=>ho 0 i.succ (by simp)) (fun i=>hl i.succ)
      (fun i=>hw i.succ) (fun i j hij=>ho i.succ j.succ (by simpa using hij))
    have hhead : max 0 (e 0-l 0)≤hi-l 0+c :=
      max_le (by linarith [hw 0,he 0]) (by linarith [he 0])
    rw [Fin.sum_univ_succ]
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith

theorem good_large_window_count {w : ℕ} (G : Finset (Fin w))
    (e l : Fin w→ℝ) (lo hi c k : ℝ)
    (hc : 0≤c) (hk : 0<k) (hlohi : lo≤hi)
    (he : ∀i∈G,e i≤hi) (hl : ∀i∈G,lo≤l i)
    (hw : ∀i∈G,l i≤e i+c)
    (ho : ∀i∈G,∀j∈G,i<j→e j≤l i+c) :
    ((G.filter fun i=>k<e i-l i).card:ℝ)≤(hi-lo+2*(G.card:ℝ)*c)/k := by
  let a:=G.orderEmbOfFin rfl
  have H:=ordered_window_drop_sum (fun i=>e (a i)) (fun i=>l (a i)) lo hi c hc hlohi
    (fun i=>he _ (Finset.orderEmbOfFin_mem ..)) (fun i=>hl _ (Finset.orderEmbOfFin_mem ..))
    (fun i=>hw _ (Finset.orderEmbOfFin_mem ..)) (fun i j hij=>ho _
      (Finset.orderEmbOfFin_mem ..) _ (Finset.orderEmbOfFin_mem ..) (a.strictMono hij))
  have hcard : (G.filter fun i=>k<e i-l i).card=
      (Finset.univ.filter fun i : Fin G.card=>k<e (a i)-l (a i)).card := by
    symm
    apply Finset.card_bij (fun i _=>a i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.orderEmbOfFin_mem ..,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ hij
      exact a.injective hij
    · intro v hv
      have hvG := (Finset.mem_filter.mp hv).1
      let i := (G.orderIsoOfFin rfl).symm ⟨v,hvG⟩
      have hi : a i=v := congrArg Subtype.val ((G.orderIsoOfFin rfl).apply_symm_apply ⟨v,hvG⟩)
      refine ⟨i,?_,hi⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hi]
      exact (Finset.mem_filter.mp hv).2
  rw [hcard]
  apply (le_div_iff₀ hk).mpr
  calc
    _ = ∑i∈Finset.univ.filter (fun i : Fin G.card=>k<e (a i)-l (a i)),k := by simp
    _ ≤ ∑i∈Finset.univ.filter (fun i : Fin G.card=>k<e (a i)-l (a i)),max 0 (e (a i)-l (a i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact ((Finset.mem_filter.mp hi).2.le).trans (le_max_right _ _)
    _ ≤ ∑i,max 0 (e (a i)-l (a i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
    _ ≤ _ := H
end
end SharpRamseyFive.FiniteEntropy

end OAI
