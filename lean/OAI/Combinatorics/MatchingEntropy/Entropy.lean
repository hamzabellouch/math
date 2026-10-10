import OAI.Combinatorics.MatchingEntropy.Face

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def marginalEntropy (y : E → ℝ) : ℝ := entropy y

theorem entropy_eq {ι : Type uι} [Fintype ι] (p : ι → ℝ) :
    entropy p = -(∑ i, p i * Real.log (p i)) := by
  simp [entropy, Real.negMulLog, Finset.sum_neg_distrib, neg_mul]

theorem continuous_entropy {ι : Type uι} [Fintype ι] :
    Continuous (entropy : (ι → ℝ) → ℝ) := by
  unfold entropy
  fun_prop

theorem entropy_nonneg {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (mem_Icc_of_mem_probabilitySimplex hp i).1
    (mem_Icc_of_mem_probabilitySimplex hp i).2

theorem entropy_le_log_card {ι : Type uι} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) : entropy p ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have hz : Fintype.card ι = 0 := Nat.eq_zero_of_not_pos h
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hz
    simpa using hp.2
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Real.negMulLog_le_one_sub_self (mul_nonneg hnR.le (hp.1 i)))
  simp_rw [Real.negMulLog_mul] at h
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hp.2, one_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_self] at h
  change Real.negMulLog (Fintype.card ι) + (Fintype.card ι : ℝ) * entropy p ≤ 0 at h
  rw [Real.negMulLog] at h
  nlinarith

namespace LooplessGraph

omit [Fintype V] [DecidableEq V] in
theorem coordinate_mem_Icc (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) (e : E) : y e ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  constructor
  · exact Finset.sum_nonneg (fun M _ ↦ mul_nonneg (hp.1 M) (G.indicator_nonneg M e))
  · calc
      ∑ M, p M * G.indicator M e ≤ ∑ M, p M * 1 :=
        Finset.sum_le_sum (fun M _ ↦ mul_le_mul_of_nonneg_left (G.indicator_le_one M e) (hp.1 M))
      _ = 1 := by simpa using hp.2

omit [Fintype E] [DecidableEq E] in

theorem incident_vertex_sum (G : LooplessGraph V E) (e : E) :
    (∑ v, if G.Incident v e then (1 : ℕ) else 0) = 2 := by
  classical
  have he (v : V) : (if G.Incident v e then (1 : ℕ) else 0) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    by_cases hl : G.left e = v <;> by_cases hr : G.right e = v
    · exact False.elim (G.loopless e (hl.trans hr.symm))
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
    · simp [Incident, hl, hr]
  simp_rw [he, Finset.sum_add_distrib]
  simp

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem matching_incident_sum (G : LooplessGraph V E) (M : G.Matching) (v : V) :
    (∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0) = 1 := by
  classical
  obtain ⟨e, ⟨he, hv⟩, hu⟩ := M.property v
  rw [Finset.sum_eq_single e]
  · simp [hv]
  · intro e' he' hne
    have hn : ¬ G.Incident v e' := fun hv' ↦ hne (hu e' ⟨he', hv'⟩)
    simp [hn]
  · simp [he]

omit [Fintype E] [DecidableEq E] in
theorem matching_card_twice (G : LooplessGraph V E) (M : G.Matching) :
    2 * M.val.card = Fintype.card V := by
  classical
  calc
    2 * M.val.card = ∑ e ∈ M.val, ∑ v, if G.Incident v e then (1 : ℕ) else 0 := by
      simp_rw [G.incident_vertex_sum]
      simp [Nat.mul_comm]
    _ = ∑ v, ∑ e ∈ M.val, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by
      simp_rw [G.matching_incident_sum]
      simp

omit [Fintype E] [DecidableEq E] in
theorem matching_card (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) : M.val.card = m := by
  have h := G.matching_card_twice M
  omega

theorem indicator_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) (M : G.Matching) :
    ∑ e, G.indicator M e = (m : ℝ) := by
  simp [indicator, G.matching_card hV M]

theorem marginal_sum (G : LooplessGraph V E) {m : ℕ}
    (hV : Fintype.card V = 2 * m) {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (m : ℝ) := by
  obtain ⟨p, hp, rfl⟩ := (G.mem_polytope_iff y).mp hy
  simp_rw [mean]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, G.indicator_sum hV]
  rw [← Finset.sum_mul, hp.2, one_mul]

end LooplessGraph

omit [Fintype V] [DecidableEq V] in

theorem maxMatchingEntropy_attained (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, entropy p = maxMatchingEntropy G y := by
  have hc := (G.compact_feasibleLaws y).image continuous_entropy
  have hn := ((G.mem_polytope_iff y).mp hy).image entropy
  obtain ⟨p, hp, hpe⟩ := hc.sSup_mem hn
  exact ⟨p, hp, hpe⟩

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_nonneg (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) : 0 ≤ maxMatchingEntropy G y := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_nonneg hp.1

omit [Fintype V] [DecidableEq V] in
theorem maxMatchingEntropy_le_log_card (G : LooplessGraph V E) {y : E → ℝ}
    (hy : y ∈ G.polytope) :
    maxMatchingEntropy G y ≤ Real.log (Fintype.card G.Matching) := by
  obtain ⟨p, hp, he⟩ := maxMatchingEntropy_attained G hy
  rw [← he]
  exact entropy_le_log_card hp.1

omit [Fintype V] [DecidableEq V] in
theorem entropy_le_maxMatchingEntropy (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y) :
    entropy p ≤ maxMatchingEntropy G y := by
  apply le_csSup
  · exact ((G.compact_feasibleLaws y).image continuous_entropy).bddAbove
  · exact ⟨p, hp, rfl⟩

end MatchingEntropyBounds

end

end OAI
