import OAI.Probability.EntangledGames.TestMoments

namespace OAI

universe u_I

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure

lemma sum_fin_get_toList {I : Type u_I} [DecidableEq I] (c : Finset I) (f : I → ℝ) :
    (∑ j : Fin c.toList.length, f c.toList[j.val]) = ∑ i ∈ c, f i := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map, Finset.sum_map_toList]

namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

omit [Nonempty I] in
lemma fresh_sum_bound (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (∑ i ∈ cᶜ, M.mass (insert i c)) ≤
      (entangledValue G+δ/4)*M.mass c*((Fintype.card I-c.card : ℕ) : ℝ) := by
  have hl : 0 < (M.exposure c hp).l.length := by
    change 0 < cᶜ.toList.length
    simp only [Finset.length_toList, Finset.card_compl]
    omega
  have hs : Real.log ((Fintype.card (Records (A := Fin (a+1)) (B := Fin (b+1)) c) : ℝ)/(M.exposure c hp).p)/
      ((M.exposure c hp).l.length : ℝ) ≤ δ^8/(2:ℝ)^80 := by
    simpa only [exposure, card_records, Fintype.card_fin, Nat.cast_pow, Finset.length_toList, Finset.card_compl] using hsmall
  have hh := conditional_rounding_small G (M.exposure c hp) hμ (M.refinement c hp) hl hδ hδ1 hs
  rw [← hV] at hh
  simp only [M.score_eq_mass_ratio] at hh
  change (1/(cᶜ.toList.length : ℝ))*∑ j : Fin cᶜ.toList.length,
    M.mass (insert cᶜ.toList[j.val] c)/M.mass c ≤ _ at hh
  rw [sum_fin_get_toList cᶜ (fun i => M.mass (insert i c)/M.mass c), ← Finset.sum_div, Finset.length_toList, Finset.card_compl] at hh
  have hn : 0 < ((Fintype.card I-c.card : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hc
  rw [one_div, inv_mul_eq_div] at hh
  have hm := (div_le_iff₀ hp).mp ((div_le_iff₀ hn).mp hh)
  nlinarith

lemma good_event_step (c : Finset I) (hp : 0 < M.mass c) (hc : c.card < Fintype.card I)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : (c.card : ℝ) ≤ δ*(Fintype.card I : ℝ)/4)
    (hsmall : Real.log ((((a+1)*(b+1) : ℕ) : ℝ)^c.card/M.mass c) /
      ((Fintype.card I-c.card : ℕ) : ℝ) ≤ δ^8/(2:ℝ)^80) :
    (uniform (R := I)).avg (fun i => M.mass (insert i c)) ≤ (entangledValue G+δ/2)*M.mass c := by
  have hf := M.fresh_sum_bound G hμ hV c hp hc hδ hδ1 hsmall
  have hcBound : (∑ i ∈ c, M.mass (insert i c)) ≤ (c.card : ℝ)*M.mass c := by
    calc
      _ ≤ ∑ _i ∈ c, M.mass c := Finset.sum_le_sum (fun i _ => M.mass_insert_le c i)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hv : 0 ≤ entangledValue G+δ/4 := by linarith [entangledValue_nonneg G]
  have hcard : ((Fintype.card I-c.card : ℕ) : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Nat.sub_le (Fintype.card I) c.card
  have hsum := add_le_add hcBound (hf.trans (mul_le_mul_of_nonneg_left hcard (mul_nonneg hv hp.le)))
  rw [Finset.sum_add_sum_compl] at hsum
  have hn : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [uniform_avg, one_div, inv_mul_eq_div]
  apply (div_le_iff₀ hn).mpr
  have hsz := mul_le_mul_of_nonneg_right hsize hp.le
  nlinarith

omit hμ hV [Nonempty m] [Nonempty n] in
lemma mean_eq_first_test : M.joint.avg (Tests.rate M.winsAt) =
    (uniform (R := I)).avg (fun i => M.mass (insert i ∅)) := by
  unfold Tests.rate
  rw [avg_comm]
  congr 1
  funext i
  unfold mass
  congr 1
  funext ω
  simp [indicator]

lemma unconditional_rate_le_value : M.joint.avg (Tests.rate M.winsAt) ≤ entangledValue G := by
  rw [M.mean_eq_first_test]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < min ε 1 := lt_min hε zero_lt_one
  have hδ1 : min ε 1 ≤ 1 := min_le_right _ _
  have hh := M.good_event_step G hμ hV ∅ (by rw [M.mass_empty]; norm_num)
    (by simpa using Fintype.card_pos (α := I)) hδ hδ1 (by simp; positivity) (by
      simp only [Finset.card_empty, pow_zero, M.mass_empty, div_one, Real.log_one, zero_div]
      positivity)
  rw [M.mass_empty, mul_one] at hh
  have hε' := min_le_left ε 1
  linarith

end RepeatedModel
end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma testing_parameters_good {δ k d p : ℝ} {c : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < k) (hd : 1 ≤ d)
    (hc : (c : ℝ) ≤ δ^9*k/((2:ℝ)^90*(1+Real.log d)))
    (hp : Real.exp (-(δ^8*k/(2:ℝ)^83)) ≤ p) :
    (c : ℝ) ≤ δ*k/4 ∧ (c : ℝ) < k ∧
      Real.log (d^c/p)/(k-(c : ℝ)) ≤ δ^8/(2:ℝ)^80 := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg hd
  have hD : 0 < (2:ℝ)^90*(1+Real.log d) := by positivity
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
  have hc' := (le_div_iff₀ hD).mp hc
  have h9 : δ^9 ≤ δ := by simpa using pow_le_pow_of_le_one hδ.le hδ1 (show 1 ≤ 9 by omega)
  have h98 : δ^9 ≤ δ^8 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h9k := mul_le_mul_of_nonneg_right h9 hk.le
  have h98k := mul_le_mul_of_nonneg_right h98 hk.le
  have hcd : (c : ℝ)*(2:ℝ)^90 ≤ δ^9*k := by
    nlinarith [mul_nonneg hc0 hlog]
  have hsize : (c : ℝ) ≤ δ*k/4 := by nlinarith
  have hhalf : (c : ℝ) ≤ k/2 := by nlinarith
  have hck : (c : ℝ) < k := by linarith
  have hp0 : 0 < p := (Real.exp_pos _).trans_le hp
  have hlp := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlp
  have hlc : Real.log (d^c/p) ≤ δ^8*k/(2:ℝ)^82 := by
    rw [Real.log_div (pow_ne_zero _ hd0.ne') hp0.ne', Real.log_pow]
    have hclog : (c : ℝ)*Real.log d ≤ δ^8*k/(2:ℝ)^90 := by
      nlinarith
    nlinarith [mul_nonneg (pow_nonneg hδ.le 8) hk.le]
  refine ⟨hsize, hck, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr hck)).mpr
  have hz : 0 ≤ δ^8 := pow_nonneg hδ.le 8
  have hh := mul_le_mul_of_nonneg_left hhalf hz
  nlinarith

end ThresholdParallelRepetition

end

end OAI
