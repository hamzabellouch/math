import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensoring
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessScales

namespace OAI

namespace Balanced.Selection.Process.CensoredJumps

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def censoredDomainCount (q : ℕ) (G : Input I V) (S : State I V)
    (i : I) (w : V) (flags : V → Bool) : ℕ :=
  if (((thinned G S w flags) ∩ domain G S i).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)
  then ((survivors G S w flags) ∩ domain G S i).card
  else (domain G S i).card

def censoredDegreeCount (q : ℕ) (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) : ℕ :=
  if w ∉ G.exceptional v ∧
      (((thinned G S w flags) ∩ neighbors G v).card : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)
  then degree G (update G S i w flags) v
  else degree G S v

omit [Fintype I] in

theorem domain_subset_slotVertices (G : Input I V) (S : State I V) (i : I) :
    domain G S i ⊆ slotVertices G i := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩

theorem domain_card_le_order {G : Input I V} {q : ℕ} {c C : ℝ}
    (hG : GraphBounds G q c C) (S : State I V) (i : I) :
    ((domain G S i).card : ℝ) ≤ q := by
  exact (Nat.cast_le.mpr (Finset.card_le_card (domain_subset_slotVertices G S i))).trans
    (Nat.cast_le.mpr (hG.2.2.1 i).2)

theorem current_degree_le_budget {G : Input I V} {q : ℕ} {c C : ℝ}
    (hG : GraphBounds G q c C) (S : State I V) (v : V) :
    (degree G S v : ℝ) ≤ C * q := by
  exact (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans
    (hG.2.2.2.1 v)

omit [Fintype I] [Fintype V] in

theorem censoredDomainCount_le (q : ℕ) (G : Input I V) (S : State I V)
    (i : I) (w : V) (flags : V → Bool) :
    censoredDomainCount q G S i w flags ≤ (domain G S i).card := by
  unfold censoredDomainCount
  split_ifs
  · exact Finset.card_le_card Finset.inter_subset_right
  · exact le_rfl

theorem abs_censoredDomainCount_sub_le
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    |(censoredDomainCount q G S i w flags : ℝ) - ((domain G S i).card : ℝ)| ≤
      2 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  unfold censoredDomainCount
  split_ifs with hthin
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
      (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)))]
    exact domain_loss_le_two_mul_rpow hG S hi w flags hthin
  · simp only [sub_self, abs_zero]
    positivity

omit [Fintype I] in

theorem censoredDegreeCount_le (q : ℕ) (G : Input I V) (S : State I V)
    (i : I) (w v : V) (flags : V → Bool) :
    censoredDegreeCount q G S i w v flags ≤ degree G S v := by
  unfold censoredDegreeCount
  split_ifs
  · exact degree_update_le G S i w v flags
  · exact le_rfl

theorem abs_censoredDegreeCount_sub_le
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    (S : State I V) (i : I) (w v : V) (flags : V → Bool) :
    |(censoredDegreeCount q G S i w v flags : ℝ) - (degree G S v : ℝ)| ≤
      3 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  unfold censoredDegreeCount
  split_ifs with hgood
  · exact abs_degree_update_sub_le_three_mul_rpow hG S i w v flags hgood.1 hgood.2
  · simp only [sub_self, abs_zero]
    positivity

theorem abs_rescaled_censoredDomainCount_sub_le
    {p : Parameters} (hp : p.Admissible) {G : Input I V} {q t : ℕ}
    (hG : GraphBounds G q p.c p.C) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) {i : I} (hi : i ∈ S.remaining) (w : V) (flags : V → Bool) :
    |(censoredDomainCount q G S i w flags : ℝ) / p.sizeScale q (t + 1) -
        ((domain G S i).card : ℝ) / p.sizeScale q t| ≤
      (2 * (q : ℝ) ^ (1 / 8 : ℝ) + p.Pstar) / p.smin := by
  have hsize : |((domain G S i).card : ℝ)| ≤ 1 * (q : ℝ) := by
    have hnon : 0 ≤ ((domain G S i).card : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonneg hnon, one_mul]
    exact domain_card_le_order hG S i
  simpa only [one_mul] using Parameters.source_size_increment_le hp hq hPq hG.1 ht
    (abs_censoredDomainCount_sub_le hG S hi w flags) hsize

theorem abs_rescaled_censoredDegreeCount_sub_le
    {p : Parameters} (hp : p.Admissible) {G : Input I V} {q t : ℕ}
    (hG : GraphBounds G q p.c p.C) (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t + 1 ≤ p.lastMainTime q (Fintype.card I))
    (S : State I V) (i : I) (w v : V) (flags : V → Bool) :
    |(censoredDegreeCount q G S i w v flags : ℝ) / p.degreeScale q (Fintype.card I) (t + 1) -
        (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t| ≤
      (3 * (q : ℝ) ^ (1 / 8 : ℝ) + p.C * (p.Pstar + 1 / p.a)) /
        (p.smin * p.a / 3) := by
  have hsize : |(degree G S v : ℝ)| ≤ p.C * q := by
    have hnon : 0 ≤ (degree G S v : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonneg hnon]
    exact current_degree_le_budget hG S v
  exact Parameters.source_degree_increment_le hp hq hPq hG.1 ht
    (abs_censoredDegreeCount_sub_le hG S i w v flags) hsize

omit [Fintype I] in

theorem censoredDomainCount_eq_of_successor
    {q : ℕ} {G : Input I V} {S S' : State I V} {r : Noise I V}
    {j : I} (hj : j ∈ S.remaining) (hne : j ≠ r.1)
    (hout : performedResult q G S r = some S') :
    censoredDomainCount q G S j r.2.1 r.2.2 = (domain G S' j).card := by
  rw [censoredDomainCount, ite_eq_left ((postcheck_of_performedResult_some hout).1 j hj)]
  rw [← domain_update_eq_survivors_inter_domain G S hne r.2.1 r.2.2,
    update_eq_of_performedResult_some hout]

theorem censoredDegreeCount_eq_of_relevant_successor
    {G : Input I V} {q : ℕ} {c C : ℝ} (hG : GraphBounds G q c C)
    {S S' : State I V} {r : Noise I V} {v : V}
    (hw : r.2.1 ∈ domain G S r.1)
    (hout : performedResult q G S r = some S')
    (hv : v ∈ currentVertices G S') :
    censoredDegreeCount q G S r.1 r.2.1 v r.2.2 = degree G S' v := by
  rw [censoredDegreeCount, ite_eq_left (relevant_successor_uncensored hG hw hout hv),
    update_eq_of_performedResult_some hout]

end
end Balanced.Selection.Process.CensoredJumps

end OAI
