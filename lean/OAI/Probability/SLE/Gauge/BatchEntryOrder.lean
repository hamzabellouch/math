import OAI.Probability.SLE.MomentGauge
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace OAI

/-! The prescribed repeated entries occupy distinct successive positions.
Their position order agrees with decreasing prescribed radii. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge.Target

private lemma prefix_eq_sum (c : ℤ → ℕ) (hc : Set.Finite {k | 0 < c k}) (b : ℤ) :
    (∑' k : ℤ, if k < b then c k else 0) =
      ∑ k∈hc.toFinset, if k < b then c k else 0 := by
  apply tsum_eq_sum
  intro k hk
  have hz : c k=0 := by
    have hn : ¬0<c k := by
      intro h
      exact hk (by simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq] using h)
    omega
  simp only [hz,ite_self]

private lemma prefix_add_le (c : ℤ → ℕ) (hc : Set.Finite {k | 0 < c k})
    {k l : ℤ} (hkl : k < l) (hk : 0 < c k) :
    (∑' i : ℤ, if i < k then c i else 0)+c k ≤
      ∑' i : ℤ, if i < l then c i else 0 := by
  have hkS : k∈hc.toFinset := by simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq] using hk
  rw [prefix_eq_sum c hc k,prefix_eq_sum c hc l]
  have hK := Finset.sum_erase_add hc.toFinset (fun i => if i < k then c i else 0) hkS
  have hL := Finset.sum_erase_add hc.toFinset (fun i => if i < l then c i else 0) hkS
  simp only [lt_self_iff_false,ite_false,add_zero] at hK
  rw [ite_eq_left hkl] at hL
  rw [← hK,← hL]
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  by_cases hik : i < k
  · rw [ite_eq_left hik,ite_eq_left (hik.trans hkl)]
  · rw [ite_eq_right hik]
    exact Nat.zero_le _

lemma entryPosition_strict_of_key_lt (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n)
    {k l : ℤ} {j j' : ℕ} (hkl : k < l) (hj : j < multiplicity κ W n k) :
    entryPosition κ W (n,some (k,j)) < entryPosition κ W (n,some (l,j')) := by
  have h := prefix_add_le (multiplicity κ W n) (multiplicity_support_finite κ W hn hm1 hJ)
    hkl (Nat.zero_le j |>.trans_lt hj)
  simp only [entryPosition]
  omega

lemma entryPosition_injective_on_batch (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n)
    {k l : ℤ} {j j' : ℕ} (hj : j < multiplicity κ W n k)
    (hj' : j' < multiplicity κ W n l)
    (he : entryPosition κ W (n,some (k,j))=entryPosition κ W (n,some (l,j'))) :
    (k,j)=(l,j') := by
  rcases lt_trichotomy k l with hkl | rfl | hlk
  · exact False.elim ((ne_of_lt (entryPosition_strict_of_key_lt κ W hn hm1 hJ hkl hj)) he)
  · simp only [entryPosition] at he
    exact Prod.ext rfl (Nat.add_left_cancel he)
  · exact False.elim ((ne_of_lt (entryPosition_strict_of_key_lt κ W hn hm1 hJ hlk hj')) he.symm)

lemma entryRadius_lt_of_position_lt {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw)
    {n : ℕ} (hn : 1 ≤ n) {o o' : Option (ℤ × ℕ)}
    (hpos : entryPosition κ W (n,o) < entryPosition κ W (n,o')) :
    entryRadius κ W (n,o') < entryRadius κ W (n,o) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hp : (entryPosition κ W (n,o):ℝ)<entryPosition κ W (n,o') := by exact_mod_cast hpos
  have hcoef : 0 < 2*a κ*((batchLevel κ W n:ℝ)+(n:ℝ)) := by
    exact mul_pos (mul_pos (by norm_num) (internal_a_pos hκ)) (by positivity)
  unfold entryRadius
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_pos hcoef (sub_pos.mpr hp)]

/-- The repeated tests have a finite chronological enumeration, without
discarding entries whose dyadic thresholds coincide. -/
theorem ordered_repeated_batch (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1^n ≤ moment κ W n) :
    ∃ (J : ℕ) (e : Fin J → ℤ × ℕ),
      Function.Injective e ∧
      (∀ kj, kj ∈ Set.range e ↔ kj.2 < multiplicity κ W n kj.1) ∧
      StrictMono (fun i => entryPosition κ W (n,some (e i))) := by
  classical
  let hs := (repeated_entries_finite κ W hn hm1 hJ).image toLex
  let s : Finset (ℤ ×ₗ ℕ) := hs.toFinset
  let e : Fin s.card → ℤ × ℕ := fun i => ofLex (s.orderEmbOfFin rfl i)
  have he (i : Fin s.card) : (e i).2 < multiplicity κ W n (e i).1 := by
    have h := s.orderEmbOfFin_mem rfl i
    change s.orderEmbOfFin rfl i ∈ hs.toFinset at h
    rw [Set.Finite.mem_toFinset] at h
    obtain ⟨kj,hkj,heq⟩ := h
    simpa only [e,← heq,ofLex_toLex,mem_ofPred_eq] using hkj
  refine ⟨s.card,e,?_,?_,?_⟩
  · exact ofLex.injective.comp (s.orderEmbOfFin rfl).injective
  · intro kj
    constructor
    · rintro ⟨i,rfl⟩
      exact he i
    · intro hkj
      have hm : toLex kj ∈ s := by
        change toLex kj ∈ hs.toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨kj,hkj,rfl⟩
      have hr : toLex kj ∈ Set.range (s.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hm
      obtain ⟨i,hi⟩ := hr
      exact ⟨i,by simp only [e,hi,ofLex_toLex]⟩
  · intro i j hij
    have hij' := (s.orderEmbOfFin rfl).strictMono hij
    change toLex (e i) < toLex (e j) at hij'
    rw [Prod.Lex.toLex_lt_toLex] at hij'
    rcases hij' with hlt | ⟨heq,hlt⟩
    · exact entryPosition_strict_of_key_lt κ W hn hm1 hJ hlt (he i)
    · simp only [entryPosition]
      rw [heq]
      exact Nat.add_lt_add_left hlt _

end SLEExactGauge.Target

end

end OAI
