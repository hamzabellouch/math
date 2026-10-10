import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestDistance

namespace OAI

namespace MetricKMedianRecovery.CoincidentCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma nearest_insert_equal (x : X) (Q : Finset X) (i f : X)
    (h : dist x i = dist x f) :
    nearestDistance x (insert i Q) = nearestDistance x (insert f Q) := by
  have hh (i f : X) (h : dist x i = dist x f) :
      nearestDistance x (insert i Q) ≤ nearestDistance x (insert f Q) := by
    obtain ⟨g,hg,he⟩ := nearestDistance_attained x (insert f Q) (Finset.insert_nonempty _ _)
    rw [he]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (nearestDistance_le_mem x (insert i Q) i (Finset.mem_insert_self _ _)).trans h.le
    · exact nearestDistance_le_mem x (insert i Q) g (Finset.mem_insert_of_mem hg)
  exact le_antisymm (hh i f h) (hh f i h.symm)

lemma active_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (j : D) :
    activeAt loc t z (insert i Q) j ↔ activeAt loc t z (insert f Q) j := by
  simp only [activeAt,Finset.forall_mem_insert,h j]

lemma clipped_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (j : D) :
    clippedAt loc t z (insert i Q) j = clippedAt loc t z (insert f Q) j := by
  simp only [clippedAt,Finset.insert_nonempty,ite_true,nearest_insert_equal _ _ _ _ (h j)]

lemma admissible_insert_equal (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) :
    admissibleBids loc t K v z (insert i Q) k tau ↔
      admissibleBids loc t K v z (insert f Q) k tau := by
  simp only [admissibleBids,active_insert_equal loc t z Q i f h,
    Finset.forall_mem_insert,h]

variable [Fintype D]

lemma payment_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) :
    openingPayment loc t z (insert i Q) k tau = openingPayment loc t z (insert f Q) k tau := by
  classical
  simp only [openingPayment,active_insert_equal loc t z Q i f h,
    nearest_insert_equal _ _ _ _ (h _)]

lemma dual_insert_equal (loc : D → X) (t z : ℝ) (Q : Finset X) (i f k : X)
    (h : ∀ j, dist (loc j) i = dist (loc j) f) (tau : D → ℝ) (a : D) :
    openingDual loc t z (insert i Q) k tau a = openingDual loc t z (insert f Q) k tau a := by
  classical
  simp only [openingDual,active_insert_equal loc t z Q i f h]

theorem openable_insert_equal (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (i f k : X) (h : ∀ j, dist (loc j) i = dist (loc j) f) :
    etaOpenable loc F (insert i Q) t K v z lam eta k ↔
      etaOpenable loc F (insert f Q) t K v z lam eta k := by
  simp only [etaOpenable,admissible_insert_equal loc t K v z Q i f _ h,
    payment_insert_equal loc t z Q i f _ h,dual_insert_equal loc t z Q i f _ h,
    active_insert_equal loc t z Q i f h]

omit [DecidableEq X] in

lemma payment_zero (loc : D → X) (t K v z : ℝ) (Q : Finset X) (i f : X)
    (hf : f ∈ Q) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ t) (tau : D → ℝ) (hb : admissibleBids loc t K v z Q i tau) :
    openingPayment loc t z Q i tau = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  change max ((if activeAt loc t z Q j then tau j else t*nearestDistance (loc j) Q)
    -t*dist i (loc j)) 0 = 0
  apply max_eq_right
  by_cases hj : activeAt loc t z Q j
  · rw [ite_eq_left hj]
    have hh := (hb j hj).2.2.1 f hf
    rw [← h j,dist_comm (loc j) i] at hh
    linarith only [hh]
  · rw [ite_eq_right hj]
    have hh := mul_le_mul_of_nonneg_left (nearestDistance_le_mem (loc j) Q f hf) ht
    rw [← h j,dist_comm (loc j) i] at hh
    linarith only [hh]

omit [DecidableEq X] in
lemma not_openable (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (i f : X) (hf : f ∈ Q) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ t) (hlam : 0 < lam-(Fintype.card D:ℝ)*eta) :
    ¬etaOpenable loc F Q t K v z lam eta i := by
  rintro ⟨tau,hb,hpay,_⟩
  rw [payment_zero loc t K v z Q i f hf h ht tau hb] at hpay
  exact (not_lt_of_ge hpay) hlam

theorem maximal_replace (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (i f : X) (h : ∀ j, dist (loc j) i = dist (loc j) f)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hmax : ∀ k ∈ F, k ∉ insert i Q →
      ¬etaOpenable loc F (insert i Q) (1-3*v) (1+v^2) v z lam 0 k) :
    ∀ k ∈ F, k ∉ insert f Q →
      ¬etaOpenable loc F (insert f Q) (1-3*v) (1+v^2) v z lam 0 k := by
  intro k hk hkn
  by_cases hki : k = i
  · subst k
    exact not_openable loc F (insert f Q) (1-3*v) (1+v^2) v z lam 0 i f
      (Finset.mem_insert_self _ _) h ht (by simpa only [mul_zero,sub_zero] using hlam)
  · intro hop
    have hn : k ∉ insert i Q := by
      simpa only [Finset.mem_insert,not_or] using ⟨hki,fun hkQ => hkn (Finset.mem_insert_of_mem hkQ)⟩
    exact hmax k hk hn ((openable_insert_equal loc F Q (1-3*v) (1+v^2) v z lam 0 i f k h).mpr hop)

omit [Fintype D] [PseudoMetricSpace X] in

lemma paid_count (F Q : Finset X) (i f : X) (hi : i ∈ F) (hin : i ∉ Q) (hf : f ∉ F) :
    (F ∩ insert i Q).card = (F ∩ insert f Q).card+1 := by
  have he : F ∩ insert i Q = insert i (F ∩ Q) := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hF,hx | hQ⟩
      · exact Or.inl hx
      · exact Or.inr ⟨hF,hQ⟩
    · rintro (rfl | ⟨hF,hQ⟩)
      · exact ⟨hi,Or.inl rfl⟩
      · exact ⟨hF,Or.inr hQ⟩
  have hf' : F ∩ insert f Q = F ∩ Q := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_insert]
    constructor
    · rintro ⟨hF,rfl | hQ⟩
      · exact (hf hF).elim
      · exact ⟨hF,hQ⟩
    · intro hx
      exact ⟨hx.1,Or.inr hx.2⟩
  rw [he,hf',Finset.card_insert_of_notMem (fun h => hin (Finset.mem_inter.mp h).2)]

end MetricKMedianRecovery.CoincidentCopy

end OAI
