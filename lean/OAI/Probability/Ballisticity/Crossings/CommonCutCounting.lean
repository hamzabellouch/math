import Mathlib
import OAI.Probability.Ballisticity.Estimates.ObservedBudget

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def smallCommonCount {d : ℕ} (e f : Direction d) (s : ℝ) (H : ℕ)
    (P : Path d × Path d) : ℕ :=
  ∑ j ∈ Finset.range H, if P ∈ SmallCommonLayer e f s (signedHeight e (P.1 0)+j) then 1 else 0

lemma smallCommonCount_zero {d : ℕ} (e f : Direction d) (s : ℝ) (P : Path d × Path d) :
    smallCommonCount e f s 0 P=0 := by simp only [smallCommonCount,Finset.range_zero,Finset.sum_empty]

lemma smallCommonCount_mono {d : ℕ} (e f : Direction d) (s : ℝ) (P : Path d × Path d) :
    Monotone (fun H => smallCommonCount e f s H P) := by
  intro H J hHJ
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hHJ) (fun _ _ _ => Nat.zero_le _)

lemma smallCommonCount_le {d : ℕ} (e f : Direction d) (s : ℝ) (H : ℕ)
    (P : Path d × Path d) : smallCommonCount e f s H P ≤ H := by
  calc
    _ ≤ ∑ _ ∈ Finset.range H, (1:ℕ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> omega
    _ = H := by simp

lemma smallCommonCount_eq_allocated {d : ℕ} (e f : Direction d) (s : ℝ)
    (P : Path d × Path d) (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (hD : P.1 ∈ NoDrop (realPosition (step e)) (P.1 0))
    (hE : P.2 ∈ NoDrop (realPosition (step e)) (P.2 0))
    (hnn : ∀ n, ∃ g, P.1 (n+1)=P.1 n+step g)
    (hmm : ∀ n, ∃ g, P.2 (n+1)=P.2 n+step g) (n : ℕ) :
    smallCommonCount e f s (signedHeight e (P.1 n)-signedHeight e (P.1 0)).toNat P=
      (allocatedSmallCuts e f s P n).card := by
  simp only [smallCommonCount,allocatedSmallCuts,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smallCommonLayer_iff_physical e f s P hxy hD hE hnn hmm]
  split_ifs <;> rfl

lemma smallCommonCount_add_suffix {d : ℕ} (e f : Direction d) (s : ℝ)
    (P : Path d × Path d) {n m a : ℕ}
    (hc : CommonTrueRecord (realPosition (step e)) P n m)
    (ha : signedHeight e (P.1 n)=signedHeight e (P.1 0)+a) (L : ℕ) :
    smallCommonCount e f s (a+L) P=smallCommonCount e f s a P+
      smallCommonCount e f s L (commonPairSuffix n m P) := by
  simp only [smallCommonCount,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hH : signedHeight e (P.1 n) ≤ signedHeight e (P.1 0)+(a+j) := by
    rw [ha]
    omega
  have he := smallCommonLayer_suffix_iff e f s P hc hH
  have hpos : signedHeight e ((commonPairSuffix n m P).1 0)+j =
      signedHeight e (P.1 0)+(a+j) := by
    simp only [commonPairSuffix,Nat.add_zero,ha,add_assoc]
  rw [hpos,he,Nat.cast_add]

def BoundedCommonGaps {d : ℕ} (e f : Direction d) (R : ℝ) (H : ℕ)
    (P : Path d × Path d) : Prop :=
  ∀ j < H, ∀ n m,
    P.1 ∈ FirstLayerHit (signedHeight e) (signedHeight e (P.1 0)+j) n →
    P.2 ∈ FirstLayerHit (signedHeight e) (signedHeight e (P.1 0)+j) m →
    P.1 ∈ FutureNoDrop (realPosition (step e)) n →
    P.2 ∈ FutureNoDrop (realPosition (step e)) m →
    |signedCoordinate f (P.1 n-P.2 m)| < R

lemma boundedCommonGaps_of_physical {d : ℕ} (e f : Direction d) (R : ℝ) (H : ℕ)
    (P : Path d × Path d) (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (hD : P.1 ∈ NoDrop (realPosition (step e)) (P.1 0))
    (hE : P.2 ∈ NoDrop (realPosition (step e)) (P.2 0))
    (hnn : ∀ n, ∃ g, P.1 (n+1)=P.1 n+step g)
    (hmm : ∀ n, ∃ g, P.2 (n+1)=P.2 n+step g)
    (hbound : ∀ j < H, |physicalFirstHitGap (realPosition (step e)) f (P.1 0) (P.2 0) j P| < R) :
    BoundedCommonGaps e f R H P := by
  intro j hj n m hn hm _ _
  rw [← physicalFirstHitGap_at_common e f P hxy hD hE hnn hmm hn hm]
  exact hbound j hj

lemma boundedCommonGaps_origin {d : ℕ} (e f : Direction d) (R : ℝ) {H : ℕ}
    (P : Path d × Path d) (hH : 0 < H)
    (hxy : signedHeight e (P.1 0)=signedHeight e (P.2 0))
    (hD : P.1 ∈ NoDrop (realPosition (step e)) (P.1 0))
    (hE : P.2 ∈ NoDrop (realPosition (step e)) (P.2 0))
    (hb : BoundedCommonGaps e f R H P) : pairGap f (pairOrigin P) < R := by
  apply hb 0 hH 0 0
  · exact ⟨by simp,fun j hj => by omega⟩
  · exact ⟨by simpa using hxy.symm,fun j hj => by omega⟩
  · simpa only [FutureNoDrop,NoDrop,Set.mem_ofPred_eq,Nat.zero_add] using hD
  · simpa only [FutureNoDrop,NoDrop,Set.mem_ofPred_eq,Nat.zero_add] using hE

lemma boundedCommonGaps_suffix {d : ℕ} (e f : Direction d) (R : ℝ) {H a n m : ℕ}
    (P : Path d × Path d) (hc : CommonTrueRecord (realPosition (step e)) P n m)
    (ha : signedHeight e (P.1 n)=signedHeight e (P.1 0)+a)
    (hb : BoundedCommonGaps e f R H P) :
    BoundedCommonGaps e f R (H-a) (commonPairSuffix n m P) := by
  intro j hj k l hk hl hD hE
  have he : signedHeight e (P.2 m)=signedHeight e (P.1 n) := by
    have hh := hc.2.2
    rw [signedHeight_projection,signedHeight_projection] at hh
    exact_mod_cast hh.symm
  have hlevel : signedHeight e ((commonPairSuffix n m P).1 0)+j=
      signedHeight e (P.1 0)+(a+j) := by
    simp only [commonPairSuffix,Nat.add_zero,ha,add_assoc]
  have hle1 : signedHeight e (P.1 n) ≤ signedHeight e (P.1 0)+(a+j) := by rw [ha]; omega
  rw [hlevel] at hk hl
  exact hb (a+j) (by omega) (n+k) (m+l)
    ((firstLayerHit_suffix_iff_of_record e P.1 hc.1.1 hle1).mp hk)
    ((firstLayerHit_suffix_iff_of_record e P.2 hc.2.1.1 (by rwa [he])).mp hl)
    ((futureNoDrop_suffix_iff _ _ n k).mp hD) ((futureNoDrop_suffix_iff _ _ m l).mp hE)

def ValidObservation {d : ℕ} (e f : Direction d) (b R : ℝ) (K : ℕ) (k : ℝ → ℕ)
    (P : Path d × Path d) : Prop :=
  signedHeight e (P.1 0)=signedHeight e (P.2 0) ∧
  P.1 ∈ NoDrop (realPosition (step e)) (P.1 0) ∧
  P.2 ∈ NoDrop (realPosition (step e)) (P.2 0) ∧
  (∀ n, ∃ g, P.1 (n+1)=P.1 n+step g) ∧
  (∀ n, ∃ g, P.2 (n+1)=P.2 n+step g) ∧
  (pairGap f (pairOrigin P) < R →
    selectedBoundaryAt (realPosition (step e)) (observedAdvanceRule e f b K k (pairOrigin P)) P
      (selectedBoundaryTimes (realPosition (step e)) (observedAdvanceRule e f b K k (pairOrigin P)) P).1
      (selectedBoundaryTimes (realPosition (step e)) (observedAdvanceRule e f b K k (pairOrigin P)) P).2)

theorem smallCommonCount_le_observer {d : ℕ} (e f : Direction d) {b R s : ℝ}
    (hbs : b ≤ 2*s) (K : ℕ) (k : ℝ → ℕ)
    (hK : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      pairGap f i < R → 0 < observedAdvanceBound f b K k i)
    (H : ℕ) (P : Path d × Path d)
    (hvalid : ∀ N, ValidObservation e f b R K k
      ((commonCutObserver (realPosition (step e)) (fun i => pairGap f i < R)
        (observedAdvanceRule e f b K k))^[N] P))
    (hbound : BoundedCommonGaps e f R H P) :
    (smallCommonCount e f s H P : ℝ≥0∞) ≤
      observerRewardSum (commonCutObserver (realPosition (step e)) (fun i => pairGap f i < R)
        (observedAdvanceRule e f b K k)) (observedCharge e f b R s K k) H P := by
  let next := commonCutObserver (realPosition (step e)) (fun i => pairGap f i < R)
    (observedAdvanceRule e f b K k)
  induction H using Nat.strong_induction_on generalizing P with
  | h H ih =>
    cases H with
    | zero => simp only [smallCommonCount_zero,observerRewardSum,Nat.cast_zero,le_refl]
    | succ H =>
      have hv := hvalid 0
      simp only [Function.iterate_zero,Function.id_def] at hv
      obtain ⟨hxy,hD,hE,hnn,hmm,hsel⟩ := hv
      have ha := boundedCommonGaps_origin e f R P (Nat.succ_pos H) hxy hD hE hbound
      have hcut := hsel ha
      let nm := selectedBoundaryTimes (realPosition (step e))
        (observedAdvanceRule e f b K k (pairOrigin P)) P
      have hnext : next P=commonPairSuffix nm.1 nm.2 P := by
        simp only [next,commonCutObserver,ite_eq_left ha,selectedBoundarySuffix,nm]
      let a := (signedHeight e (P.1 nm.1)-signedHeight e (P.1 0)).toNat
      have haPos : 0 < a := by
        have hr := hcut.2.2.1.1.1 0 hcut.1
        rw [signedHeight_projection,signedHeight_projection] at hr
        have hr' : signedHeight e (P.1 0) < signedHeight e (P.1 nm.1) := by exact_mod_cast hr
        dsimp only [a]
        omega
      have haEq : signedHeight e (P.1 nm.1)=signedHeight e (P.1 0)+a := by
        dsimp only [a] at haPos ⊢
        omega
      have hcharge : (smallCommonCount e f s a P : ℝ≥0∞) ≤ observedCharge e f b R s K k P := by
        rw [smallCommonCount_eq_allocated e f s P hxy hD hE hnn hmm nm.1]
        exact allocatedSmallCuts_le_charge e f hbs K k P hxy ha (hK _ hxy ha) hcut
      by_cases hHa : H+1 ≤ a
      · apply hcharge.trans' (by exact_mod_cast (smallCommonCount_mono e f s P hHa)) |>.trans
        exact le_add_right le_rfl
      · have haH : a ≤ H+1 := by omega
        have he := smallCommonCount_add_suffix e f s P hcut.2.2.1 haEq (H+1-a)
        rw [Nat.add_sub_of_le haH,← hnext] at he
        have hvalid' : ∀ N, ValidObservation e f b R K k (next^[N] (next P)) := by
          intro N
          simpa only [Function.iterate_succ_apply] using hvalid (N+1)
        have hb' := boundedCommonGaps_suffix e f R P hcut.2.2.1 haEq hbound
        rw [← hnext] at hb'
        have hi := ih (H+1-a) (by omega) (next P) hvalid' hb'
        rw [he,Nat.cast_add]
        exact (add_le_add hcharge hi).trans
          (add_le_add_right (observerRewardSum_mono next (observedCharge e f b R s K k)
            (show H+1-a ≤ H by omega) (next P)) _)

end DirectionalTransience

end

end

end OAI
