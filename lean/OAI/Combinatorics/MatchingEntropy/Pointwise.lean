import OAI.Combinatorics.MatchingEntropy.RefinedVariation

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Module Matrix

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph

theorem pointwise_entropy (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    entropy x - (2 - 2 / (m : ℝ)) * complementEntropy x ≤ maxMatchingEntropy G x ∧
      maxMatchingEntropy G x ≤ entropy x := by
  obtain ⟨_⟩ := hPM
  exact ⟨refined_lower G m hm hV x hx, refined_upper G x hx⟩

omit [Fintype V] [DecidableEq V] in
theorem F_nonneg (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ entropy x := by
  exact Finset.sum_nonneg (fun e _ => Real.negMulLog_nonneg
    (G.coordinate_mem_Icc hx e).1 (G.coordinate_mem_Icc hx e).2)

omit [Fintype V] [DecidableEq V] in
theorem B_nonneg (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    0 ≤ complementEntropy x := by
  apply Finset.sum_nonneg
  intro e _
  exact Real.negMulLog_nonneg (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)
    (by linarith [(G.coordinate_mem_Icc hx e).1])

theorem B_le_order (G : LooplessGraph V E) (m : ℕ) (hV : Fintype.card V = 2 * m)
    {x : E → ℝ} (hx : x ∈ G.polytope) : complementEntropy x ≤ m := by
  rw [← G.marginal_sum hV hx]
  apply Finset.sum_le_sum
  intro e _
  simpa only [sub_sub_cancel] using
    Real.negMulLog_le_one_sub_self (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)

theorem entropy_defect (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (x : E → ℝ) (hx : x ∈ G.polytope) :
    0 ≤ entropy x - maxMatchingEntropy G x ∧
      entropy x - maxMatchingEntropy G x ≤ min (entropy x) (2 * (m : ℝ) - 2) := by
  have hb := pointwise_entropy G m hm hV hPM x hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 0 ≤ 2 - 2 / (m : ℝ) := by
    have hd : 2 / (m : ℝ) ≤ 2 := (div_le_iff₀ hmR).mpr (by linarith)
    linarith
  have heq : (2 - 2 / (m : ℝ)) * m = 2 * (m : ℝ) - 2 := by field_simp
  have hB := mul_le_mul_of_nonneg_left (B_le_order G m hV hx) hc
  rw [heq] at hB
  refine ⟨sub_nonneg.mpr hb.2, le_min ?_ ?_⟩
  · linarith [maxMatchingEntropy_nonneg G hx]
  · linarith [hb.1]

section UniformLaw
variable {I : Type uI} [Fintype I]

def uniformLaw (I : Type uI) [Fintype I] : I → ℝ := fun _ => (Fintype.card I : ℝ)⁻¹

theorem uniformLaw_simplex [Nonempty I] : uniformLaw I ∈ probabilitySimplex I := by
  have hN : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun _ => inv_nonneg.mpr (Nat.cast_nonneg _), ?_⟩
  simp [uniformLaw, hN]

theorem uniformLaw_entropy [Nonempty I] : entropy (uniformLaw I) = Real.log (Fintype.card I : ℝ) := by
  have hN : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [entropy, uniformLaw, Real.negMulLog, Real.log_inv, neg_mul_neg,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
end UniformLaw

omit [Fintype V] [DecidableEq V] in
theorem uniformMatching_mean (G : LooplessGraph V E) (hPM : Nonempty G.Matching) :
    ∃ z ∈ G.polytope, maxMatchingEntropy G z = Real.log (Fintype.card G.Matching : ℝ) := by
  let := hPM
  have hp := uniformLaw_simplex (I := G.Matching)
  have hz : G.mean (uniformLaw G.Matching) ∈ G.polytope := G.mean_mem_polytope hp
  refine ⟨_, hz, le_antisymm (maxMatchingEntropy_le_log_card G hz) ?_⟩
  rw [← uniformLaw_entropy (I := G.Matching)]
  exact entropy_le_maxMatchingEntropy G ⟨hp, rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_binaryEntropy : Continuous (binaryEntropy (E := E)) := by
  exact continuous_entropy.add (continuous_entropy.comp (by fun_prop))

theorem optimized_entropy (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∃ y ∈ G.polytope,
      (∀ z ∈ G.polytope, entropy z ≤ entropy x) ∧
      (∀ z ∈ G.polytope, binaryEntropy z ≤ binaryEntropy y) ∧
      Real.log (Fintype.card G.Matching : ℝ) ≤ entropy x ∧
      entropy x ≤ Real.log (Fintype.card G.Matching : ℝ) + 2 * (m : ℝ) - 2 ∧
      Real.log (Fintype.card G.Matching : ℝ) ≤ binaryEntropy y ∧
      binaryEntropy y ≤ Real.log (Fintype.card G.Matching : ℝ) + 3 * (m : ℝ) - 2 := by
  obtain ⟨z, hz, heq⟩ := uniformMatching_mean G hPM
  have hn : G.polytope.Nonempty := ⟨z, hz⟩
  obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope
    continuous_entropy.continuousOn.upperSemicontinuousOn
  obtain ⟨y, hy, hmaxb⟩ := UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope
    continuous_binaryEntropy.continuousOn.upperSemicontinuousOn
  have hxdef := (entropy_defect G m hm hV hPM x hx).2.trans (min_le_right _ _)
  have hydef := (entropy_defect G m hm hV hPM y hy).2.trans (min_le_right _ _)
  have hxu := maxMatchingEntropy_le_log_card G hx
  have hyu := maxMatchingEntropy_le_log_card G hy
  have hzu := refined_upper G z hz
  have hzB := B_nonneg G hz
  have hyB := B_le_order G m hV hy
  have hzx : entropy z ≤ entropy x := hmax hz
  have hzy := hmaxb hz
  change entropy z + complementEntropy z ≤ entropy y + complementEntropy y at hzy
  refine ⟨x, hx, y, hy, hmax, hmaxb, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · change _ ≤ entropy y + complementEntropy y
    linarith
  · change entropy y + complementEntropy y ≤ _
    linarith

def countBound (m k : ℕ) (N : ℝ) : Prop :=
  (k = 1 → 1 ≤ N) ∧
  (2 ≤ k → (k : ℝ)^m * (1 - 1 / (k : ℝ))^(2 * (m - 1) * (k - 1)) ≤ N ∧
    Real.exp (-2 * ((m : ℝ) - 1)) * (k : ℝ)^m ≤
      (k : ℝ)^m * (1 - 1 / (k : ℝ))^(2 * (m - 1) * (k - 1)) ∧
    (Real.exp (-2) * (k : ℝ))^m ≤ Real.exp (-2 * ((m : ℝ) - 1)) * (k : ℝ)^m)

omit [Fintype V] [DecidableEq V] in
theorem matching_nonempty_of_mem (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    Nonempty G.Matching := by
  obtain ⟨p, hp⟩ := (G.mem_polytope_iff x).mp hx
  by_contra h
  have : IsEmpty G.Matching := not_nonempty_iff.mp h
  simpa using hp.1.2

theorem entropy_uniform (G : LooplessGraph V E) {m k : ℕ}
    (hV : Fintype.card V = 2 * m) (hk : 2 ≤ k) {x : E → ℝ} (hx : x ∈ G.polytope)
    (hu : ∀ e, x e = 0 ∨ x e = 1 / (k : ℝ)) :
    entropy x = (m : ℝ) * Real.log (k : ℝ) ∧
    complementEntropy x = -(m : ℝ) * ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha (e : E) : Real.negMulLog (x e) = x e * Real.log (k : ℝ) := by
    rcases hu e with he | he
    · simp [he]
    · rw [he, one_div, Real.negMulLog, Real.log_inv]; ring
  have hb (e : E) : Real.negMulLog (1 - x e) =
      -((k : ℝ) - 1) * x e * Real.log (1 - 1 / (k : ℝ)) := by
    rcases hu e with he | he
    · simp [he]
    · rw [he, Real.negMulLog]; field_simp
  constructor
  · simp_rw [entropy, ha]
    rw [← Finset.sum_mul, G.marginal_sum hV hx]
  · simp_rw [complementEntropy, entropy, hb]
    rw [← Finset.sum_mul, ← Finset.mul_sum, G.marginal_sum hV hx]
    ring

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem finiteCount_eq_exp {m k : ℕ} (hm : 0 < m) (hk : 2 ≤ k) :
    (k : ℝ)^m * (1 - 1 / (k : ℝ))^(2 * (m - 1) * (k - 1)) =
      Real.exp ((m : ℝ) * Real.log (k : ℝ) +
        2 * ((m : ℝ) - 1) * ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ))) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have ht : 0 < 1 - 1 / (k : ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr hkR)
  have hc : 2 * ((m : ℝ) - 1) * ((k : ℝ) - 1) = ((2 * (m - 1) * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  rw [hc, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by linarith), Real.exp_log ht]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem log_uniform_loss {k : ℕ} (hk : 2 ≤ k) :
    -1 ≤ ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ)) := by
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have ht : 0 < 1 - 1 / (k : ℝ) := sub_pos.mpr ((div_lt_one hk0).mpr hkR)
  have hb := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at hb
  have hkm : 0 < (k : ℝ) - 1 := by linarith
  have heq : ((1 - 1 / (k : ℝ))⁻¹ - 1) * ((k : ℝ) - 1) = 1 := by
    field_simp; ring
  have hh := mul_le_mul_of_nonneg_right hb (by linarith : 0 ≤ (k : ℝ) - 1)
  rw [heq] at hh
  nlinarith

theorem refined_uniform_count (G : LooplessGraph V E) {m k : ℕ}
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) {x : E → ℝ} (hx : x ∈ G.polytope)
    (hu : ∀ e, x e = 0 ∨ x e = 1 / (k : ℝ)) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  have hPM := matching_nonempty_of_mem G hx
  have hN : (0 : ℝ) < Fintype.card G.Matching := by
    exact_mod_cast Fintype.card_pos_iff.mpr hPM
  refine ⟨fun _ => by exact_mod_cast Fintype.card_pos_iff.mpr hPM, fun hk => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hF, hB⟩ := entropy_uniform G hV hk hx hu
  have hl := (pointwise_entropy G m hm hV hPM x hx).1.trans (maxMatchingEntropy_le_log_card G hx)
  rw [hF, hB] at hl
  have hl' : (m : ℝ) * Real.log (k : ℝ) +
      2 * ((m : ℝ) - 1) * ((k : ℝ) - 1) * Real.log (1 - 1 / (k : ℝ)) ≤
      Real.log (Fintype.card G.Matching : ℝ) := by
    convert hl using 1
    first | rfl | (field_simp; ring)
  refine ⟨?_, ?_, ?_⟩
  · rw [finiteCount_eq_exp hm hk]
    simpa only [Real.exp_log hN] using Real.exp_le_exp.mpr hl'
  · rw [finiteCount_eq_exp hm hk]
    have heq : Real.exp (-2 * ((m : ℝ) - 1)) * (k : ℝ)^m =
        Real.exp (-2 * ((m : ℝ) - 1) + (m : ℝ) * Real.log (k : ℝ)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hk0]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (log_uniform_loss hk) (by linarith : 0 ≤ 2 * ((m : ℝ) - 1))
    nlinarith
  · rw [mul_pow, ← Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hk0.le _)
    apply Real.exp_le_exp.mpr
    linarith

theorem structural_count (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (M : Fin k → G.Matching)
    (hd : ∀ i j, i ≠ j → Disjoint (M i).val (M j).val) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  obtain ⟨x, hx, hu⟩ := selected_uniform_mean G hk M hd
  exact refined_uniform_count G hm hV hx hu

theorem regular_count (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card = k)
    (hodd : ∀ S : Finset V, Odd S.card → k ≤ (G.cut S).card) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  exact refined_uniform_count G hm hV (regular_uniform_mem G hV hk hregular hodd) (fun _ => Or.inr rfl)

omit [Fintype V] [DecidableEq E] in

theorem degree_cut_count (G : LooplessGraph V E) {k : ℕ}
    (hreg : ∀ v, (Finset.univ.filter (G.Incident v)).card = k) (S : Finset V) :
    S.card * k = 2 * (Finset.univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S)).card +
      (G.cut S).card := by
  classical
  have hp (e : E) : ((if G.left e ∈ S then (1 : ℕ) else 0) +
      (if G.right e ∈ S then 1 else 0)) =
      2 * (if G.left e ∈ S ∧ G.right e ∈ S then 1 else 0) +
        (if G.Crosses S e then 1 else 0) := by
    by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [Crosses, hl, hr]
  calc
    S.card * k = ∑ v ∈ S, (∑ e : E, if G.Incident v e then (1 : ℕ) else 0) := by
      simp [Finset.sum_boole, hreg, Finset.sum_const]
    _ = ∑ e : E, ∑ v ∈ S, if G.Incident v e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [G.incidence_sum, hp]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [Finset.sum_boole, cut]

omit [DecidableEq E] in

theorem connected_odd_cut (G : LooplessGraph V E) {m k : ℕ}
    (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card = k)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k - 1 ≤ (G.cut S).card)
    (S : Finset V) (hS : Odd S.card) : k ≤ (G.cut S).card := by
  have hsmod := Nat.odd_iff.mp hS
  have hn : S.Nonempty := Finset.card_pos.mp (by omega)
  have hp : S ≠ Finset.univ := by
    intro hh
    simp only [hh, Finset.card_univ, hV] at hsmod
    omega
  have hc := hconn S hn hp
  have heq := congrArg (fun a : ℕ => a % 2) (degree_cut_count G hregular S)
  rw [Nat.mul_mod S.card k 2, hsmod] at heq
  simp only [one_mul, Nat.mod_mod] at heq
  omega

theorem connected_regular_count (G : LooplessGraph V E) (m k : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hk : 1 ≤ k)
    (hregular : ∀ v, (Finset.univ.filter (G.Incident v)).card = k)
    (hconn : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → k - 1 ≤ (G.cut S).card) :
    countBound m k (Fintype.card G.Matching : ℝ) := by
  exact regular_count G m k hm hV hk hregular (connected_odd_cut G hV hk hregular hconn)

def weightedPartition (G : LooplessGraph V E) (β : E → ℝ) : ℝ :=
  ∑ M : G.Matching, (2 : ℝ) ^ (∑ e, β e * G.indicator M e)
def weightedObjective (β x : E → ℝ) : ℝ := entropy x / Real.log 2 + ∑ e, β e * x e

def gibbsLaw (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) : ℝ :=
  (2 : ℝ) ^ (∑ e, β e * G.indicator M e) / weightedPartition G β

omit [Fintype V] [DecidableEq V] in
theorem weightedPartition_pos (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    0 < weightedPartition G β := by
  let := hPM
  exact Finset.sum_pos (fun M _ => Real.rpow_pos_of_pos (by norm_num) _) Finset.univ_nonempty

omit [Fintype V] [DecidableEq V] in
theorem gibbsLaw_pos (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) (M : G.Matching) :
    0 < gibbsLaw G β M :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (weightedPartition_pos G hPM β)

omit [Fintype V] [DecidableEq V] in
theorem gibbsLaw_simplex (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    gibbsLaw G β ∈ probabilitySimplex G.Matching := by
  refine ⟨fun M => (gibbsLaw_pos G hPM β M).le, ?_⟩
  simp only [gibbsLaw, ← Finset.sum_div]
  exact div_self (weightedPartition_pos G hPM β).ne'

omit [Fintype V] [DecidableEq V] in
theorem gibbs_cross_entropy (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ)
    {p : G.Matching → ℝ} (hp : p ∈ probabilitySimplex G.Matching) :
    -(∑ M, p M * Real.log (gibbsLaw G β M)) =
      Real.log (weightedPartition G β) - Real.log 2 * (∑ e, β e * G.mean p e) := by
  have hl (M : G.Matching) : Real.log (gibbsLaw G β M) =
      (∑ e, β e * G.indicator M e) * Real.log 2 - Real.log (weightedPartition G β) := by
    rw [gibbsLaw, Real.log_div (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))
      (weightedPartition_pos G hPM β).ne', Real.log_rpow (by norm_num)]
  simp_rw [hl, mul_sub, ← mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hp.2, one_mul, sum_mean_assoc]
  ring

omit [Fintype V] [DecidableEq V] in
theorem gibbs_law_bound (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ)
    {p : G.Matching → ℝ} (hp : p ∈ probabilitySimplex G.Matching) :
    entropy p / Real.log 2 + (∑ e, β e * G.mean p e) ≤
      Real.log (weightedPartition G β) / Real.log 2 := by
  have h := entropy_le_crossEntropy (gibbsLaw_simplex G hPM β) hp
    (fun M hzero => ((gibbsLaw_pos G hPM β M).ne' hzero).elim)
  rw [gibbs_cross_entropy G hPM β hp] at h
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (le_div_iff₀ hlog).mpr
  rw [add_mul, div_mul_cancel₀ _ hlog.ne']
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem gibbs_law_equality (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    entropy (gibbsLaw G β) / Real.log 2 + (∑ e, β e * G.mean (gibbsLaw G β) e) =
      Real.log (weightedPartition G β) / Real.log 2 := by
  have h := gibbs_cross_entropy G hPM β (gibbsLaw_simplex G hPM β)
  rw [← entropy_eq] at h
  rw [h]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp
  ring

omit [Fintype V] [DecidableEq V] in

theorem gibbs_variational (G : LooplessGraph V E) (hPM : Nonempty G.Matching) (β : E → ℝ) :
    gibbsLaw G β ∈ probabilitySimplex G.Matching ∧
    maxMatchingEntropy G (G.mean (gibbsLaw G β)) / Real.log 2 +
        (∑ e, β e * G.mean (gibbsLaw G β) e) = Real.log (weightedPartition G β) / Real.log 2 ∧
    ∀ x ∈ G.polytope, maxMatchingEntropy G x / Real.log 2 + (∑ e, β e * x e) ≤
      Real.log (weightedPartition G β) / Real.log 2 := by
  have hp := gibbsLaw_simplex G hPM β
  have hx := G.mean_mem_polytope hp
  have hu : ∀ x ∈ G.polytope, maxMatchingEntropy G x / Real.log 2 + (∑ e, β e * x e) ≤
      Real.log (weightedPartition G β) / Real.log 2 := by
    intro x hx
    obtain ⟨p, hp, hopt⟩ := maxMatchingEntropy_attained G hx
    rw [← hopt, ← hp.2]
    exact gibbs_law_bound G hPM β hp.1
  refine ⟨hp, le_antisymm (hu _ hx) ?_, hu⟩
  rw [← gibbs_law_equality G hPM β]
  exact add_le_add (div_le_div_of_nonneg_right (entropy_le_maxMatchingEntropy G ⟨hp, rfl⟩)
    (Real.log_pos (by norm_num)).le) le_rfl

theorem weighted_count (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (hPM : Nonempty G.Matching)
    (β : E → ℝ) :
    ∃ x ∈ G.polytope, (∀ y ∈ G.polytope, weightedObjective β y ≤ weightedObjective β x) ∧
      weightedObjective β x - (2 * (m : ℝ) - 2) / Real.log 2 ≤
        Real.log (weightedPartition G β) / Real.log 2 ∧
      Real.log (weightedPartition G β) / Real.log 2 ≤ weightedObjective β x := by
  obtain ⟨hp, heq, hu⟩ := gibbs_variational G hPM β
  have hz := G.mean_mem_polytope hp
  have hcont : Continuous (weightedObjective β) := by
    unfold weightedObjective
    exact (continuous_entropy.div_const _).add (by fun_prop)
  obtain ⟨x, hx, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨_, hz⟩ G.compact_polytope
    hcont.continuousOn.upperSemicontinuousOn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨x, hx, hmax, ?_, ?_⟩
  · have hd := (entropy_defect G m hm hV hPM x hx).2.trans (min_le_right _ _)
    have hd' := div_le_div_of_nonneg_right hd hlog.le
    have huu := hu x hx
    dsimp only [weightedObjective]
    rw [sub_div] at hd'
    linarith
  · rw [← heq]
    apply le_trans _ (hmax hz)
    exact add_le_add (div_le_div_of_nonneg_right (refined_upper G _ hz) hlog.le) le_rfl

end MatchingEntropyBounds.Refined

end

end OAI
