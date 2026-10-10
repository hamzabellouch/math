import OAI.Probability.ThorpShuffle.BlockLaws

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp
open scoped Classical

lemma law_complexSign_zero (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    (∑ g : State d, (law d t g : ℂ) * Specht.complexSign g) = 0 := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  have h := congrArg (fun x : ℝ => (x : ℂ)) (Parity.law_sign_zero d t)
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero, Parity.sign,
    Specht.complexSign_eq, Complex.ofReal_intCast] using h

namespace Block
open Thorp.Fourier Thorp.Specht

def fullRate (d : ℕ) : ℝ :=
  8 * discarded d + (1/2 : ℝ) * Real.sqrt
    (2 * (2 * discarded d)^16 + (96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))

lemma exceptional_cube_tendsto :
    Tendsto (fun d : ℕ => exceptionalReciprocalSum (2^d)) atTop (nhds 0) :=
  exceptionalReciprocalSum_tendsto.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

lemma fullRate_tendsto : Tendsto fullRate atTop (nhds 0) := by
  change Tendsto (fun d : ℕ => 8 * discarded d + (1/2 : ℝ) * Real.sqrt
    (2 * (2 * discarded d)^16 + (96 : ℝ)^8 * exceptionalReciprocalSum (2^(d+1+2)))) atTop (nhds 0)
  have he := exceptional_cube_tendsto.comp (tendsto_add_atTop_nat 3)
  have hb := ((discarded_tendsto.const_mul 2).pow 16).const_mul 2
  have hs := (hb.add (he.const_mul ((96:ℝ)^8))).sqrt
  simpa only [Nat.add_assoc, Function.comp_def, mul_zero, zero_pow (by decide : 16 ≠ 0),
    add_zero, Real.sqrt_zero] using (discarded_tendsto.const_mul 8).add (hs.const_mul (1/2 : ℝ))

lemma reciprocal_atMost_three :
    ∀ᶠ d : ℕ in atTop, (permutationFamily (Position d)).reciprocalSum ≤ 3 := by
  have he : ∀ᶠ d : ℕ in atTop, exceptionalReciprocalSum (2^d) < 1 :=
    (tendsto_order.1 exceptional_cube_tendsto).2 1 (by norm_num)
  filter_upwards [he] with d hd
  have h := full_reciprocal_bound (2^d)
  have hc : (permutationFamily (Position d)).reciprocalSum = (symmetricFamily (2^d)).reciprocalSum := by
    change (symmetricFamily (Fintype.card (Position d))).reciprocalSum = _
    rw [card_position]
  rw [hc]
  linarith

lemma distance_eight_eventually :
    ∀ᶠ d : ℕ in atTop, distance (d+1+2) (1600*(d+1+2)) ≤ fullRate d := by
  have hd : ∀ᶠ d : ℕ in atTop, discarded d ≤ 1/2 :=
    ((tendsto_order.1 discarded_tendsto).2 (1/2) (by norm_num)).mono (fun _ h => h.le)
  filter_upwards [hd, reciprocal_atMost_three, eventually_ge_atTop 1] with d hδ hR hd1
  have hn : 16 ≤ Fintype.card (Position (d+1+2)) := by
    rw [card_position]
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^(d+1+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let : Nontrivial (Position (d+1+2)) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hbound := trimmed_eight_tv hn (embedding (eightEquiv d)) (law (d+1+2) (200*(d+1+2)))
    (law_nonneg (d+1+2) (200*(d+1+2))) (law_sum (d+1+2) (200*(d+1+2)))
    (law_complexSign_zero _ _ (by omega) (by omega)) hδ
  have hpower : law (d+1+2) (1600*(d+1+2)) = realPower (law (d+1+2) (200*(d+1+2))) 8 := by
    rw [show 1600*(d+1+2) = 8 * (200*(d+1+2)) by omega]
    exact law_realPower (d+1+2) (200*(d+1+2)) 8
  change tv (law (d+1+2) (1600*(d+1+2)))
    (fun _ => 1 / (Fintype.card (State (d+1+2)) : ℝ)) ≤ fullRate d
  simp only [one_div]
  rw [hpower]
  apply hbound.trans
  unfold fullRate
  refine add_le_add (le_refl _) ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  refine add_le_add (le_refl _) ?_
  rw [card_position]
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun p _ => by
    change 0 ≤ (if 0 < defect p then inverseDegree p else 0)
    split_ifs <;> first | exact inverseDegree_nonneg p | exact le_rfl))
  apply pow_le_pow_left₀ (mul_nonneg (by norm_num) (permutationFamily (Position d)).reciprocalSum_nonneg)
  linarith

lemma full_mixing_shift :
    Tendsto (fun d : ℕ => distance (d+1+2) (1600*(d+1+2))) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun d => by unfold distance tv; positivity))
    distance_eight_eventually fullRate_tendsto

end Block
end Thorp

end

end OAI
