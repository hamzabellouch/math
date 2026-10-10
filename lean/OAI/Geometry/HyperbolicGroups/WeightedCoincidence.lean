import Mathlib

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace Coincidence

variable {V C E : Type*} [Fintype V] [DecidableEq C]

/-- Coincidence rank on an actual subset of field positions. -/
def rankOn (c : V → C) (s : Finset V) : ℕ := s.card - (s.image c).card

/-- A maximum-weight representative of each nonempty unsigned class. -/
def maxRepresentative (c : V → C) (w : V → ℕ) (v : V) : V :=
  Classical.choose (Finset.exists_max_image (Finset.univ.filter (fun x => c x = c v)) w
    (by exact ⟨v,by simp⟩))

lemma maxRepresentative_mem (c : V → C) (w : V → ℕ) (v : V) :
    c (maxRepresentative c w v) = c v := by
  have h := (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ.filter (fun x => c x = c v)) w (by exact ⟨v,by simp⟩))).1
  exact (Finset.mem_filter.mp h).2

lemma le_maxRepresentative (c : V → C) (w : V → ℕ) (v : V) :
    w v ≤ w (maxRepresentative c w v) := by
  exact (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ.filter (fun x => c x = c v)) w (by exact ⟨v,by simp⟩))).2 v (by simp)

lemma maxRepresentative_eq (c : V → C) (w : V → ℕ) {u v : V} (h : c u = c v) :
    maxRepresentative c w u = maxRepresentative c w v := by
  unfold maxRepresentative
  congr 2
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [h]

lemma maxRepresentative_idem (c : V → C) (w : V → ℕ) (v : V) :
    maxRepresentative c w (maxRepresentative c w v) = maxRepresentative c w v :=
  maxRepresentative_eq c w (maxRepresentative_mem c w v)

variable [DecidableEq V]

/-- The representative/nonrepresentative partition computes rank at every
level. A maximal position remains selected whenever any class member does. -/
lemma rank_level (c : V → C) (w : V → ℕ) (j : ℕ) :
    rankOn c (Finset.univ.filter (fun v => j < w v)) =
      (Finset.univ.filter (fun v => j < w v ∧ v ≠ maxRepresentative c w v)).card := by
  let s : Finset V := Finset.univ.filter (fun v => j < w v)
  let t := s.filter (fun v => v = maxRepresentative c w v)
  have ht : s.image c = t.image c := by
    ext a
    constructor
    · intro ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      refine Finset.mem_image.mpr ⟨maxRepresentative c w v,?_,maxRepresentative_mem c w v⟩
      simp only [t,Finset.mem_filter,s,Finset.mem_univ,true_and]
      exact ⟨lt_of_lt_of_le (Finset.mem_filter.mp hv).2 (le_maxRepresentative c w v),
        (maxRepresentative_idem c w v).symm⟩
    · intro ha
      obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,hv'⟩
  have hi : Set.InjOn c t := by
    intro u hu v hv hc
    rw [(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2]
    exact maxRepresentative_eq c w hc
  have hh := Finset.card_filter_add_card_filter_not
    (s := s) (p := fun v => v = maxRepresentative c w v)
  change s.card - (s.image c).card = _
  rw [ht,Finset.card_image_of_injOn hi]
  have hfilter : s.filter (fun v => ¬v = maxRepresentative c w v) =
      Finset.univ.filter (fun v => j < w v ∧ v ≠ maxRepresentative c w v) := by
    ext v
    simp [s]
  change t.card + _ = s.card at hh
  rw [hfilter] at hh
  omega

omit [Fintype V] [DecidableEq V] in
lemma layer_cake (s : Finset V) (w : V → ℕ) (K : ℕ) (hK : ∀ v ∈ s, w v ≤ K) :
    ∑ j ∈ Finset.range K, (s.filter (fun v => j < w v)).card = ∑ v ∈ s, w v := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hf : (Finset.range K).filter (fun j => j < w v) = Finset.range (w v) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    have hh := hK v hv
    omega
  rw [← Finset.sum_filter,hf]
  simp

/-- Exact integer layer-cake identity. -/
theorem sum_rank_levels (c : V → C) (w : V → ℕ) (K : ℕ) (hK : ∀ v, w v ≤ K) :
    ∑ j ∈ Finset.range K, rankOn c (Finset.univ.filter (fun v => j < w v)) =
      ∑ v ∈ Finset.univ.filter (fun v => v ≠ maxRepresentative c w v), w v := by
  simp_rw [rank_level]
  have he (j : ℕ) : Finset.univ.filter (fun v => j < w v ∧ v ≠ maxRepresentative c w v) =
      (Finset.univ.filter (fun v => v ≠ maxRepresentative c w v)).filter (fun v => j < w v) := by
    ext v
    simp [and_comm]
  simp_rw [he]
  exact layer_cake _ w K (fun v _ => hK v)

/-- Each letter contact is charged to an endpoint other than the class maximum.
This uses actual side capacities, not a forest assumption on the contact graph. -/
def contactCharge (c : V → C) (w : V → ℕ) (l r : E → V) (e : E) : V :=
  if l e = maxRepresentative c w (l e) then r e else l e

lemma contactCharge_endpoint (c : V → C) (w : V → ℕ) (l r : E → V) (e : E) :
    contactCharge c w l r e = l e ∨ contactCharge c w l r e = r e := by
  unfold contactCharge
  split_ifs <;> simp

lemma contactCharge_not_max (c : V → C) (w : V → ℕ) (l r : E → V)
    (hneq : ∀ e, l e ≠ r e) (hc : ∀ e, c (l e) = c (r e)) (e : E) :
    contactCharge c w l r e ≠ maxRepresentative c w (contactCharge c w l r e) := by
  unfold contactCharge
  split_ifs with h
  · intro h'
    apply hneq e
    exact h.trans ((maxRepresentative_eq c w (hc e)).trans h'.symm)
  · exact h

variable [Fintype E]

/-- The contact bound, valid for arbitrary cycles, multiple edges and repeats
of cell copies. Normality is precisely the inequality of the two field indices. -/
theorem contacts_le_weighted_rank (c : V → C) (w : V → ℕ) (l r : E → V)
    (hneq : ∀ e, l e ≠ r e) (hc : ∀ e, c (l e) = c (r e))
    (hcap : ∀ v, (Finset.univ.filter (fun e => l e = v ∨ r e = v)).card ≤ w v)
    (K : ℕ) (hK : ∀ v, w v ≤ K) :
    Fintype.card E ≤ ∑ j ∈ Finset.range K,
      rankOn c (Finset.univ.filter (fun v => j < w v)) := by
  rw [sum_rank_levels c w K hK]
  let f := contactCharge c w l r
  let s := Finset.univ.filter (fun v => v ≠ maxRepresentative c w v)
  have hf (e : E) : f e ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact contactCharge_not_max c w l r hneq hc e
  have hcard : Fintype.card E = ∑ v ∈ s, (Finset.univ.filter (fun e => f e = v)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [hf]
  rw [hcard]
  apply Finset.sum_le_sum
  intro v hv
  apply le_trans (Finset.card_le_card ?_) (hcap v)
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(contactCharge_endpoint c w l r e).imp
    (fun h => h.symm.trans hh) (fun h => h.symm.trans hh)⟩

end Coincidence
end HyperbolicObstruction
end
end

section

end
end

end OAI
