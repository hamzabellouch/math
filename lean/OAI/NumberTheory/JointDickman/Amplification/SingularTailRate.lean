import OAI.NumberTheory.JointDickman.Amplification.SingularSeriesTail

namespace OAI

/-! # A power bound for the singular-series tail at the manuscript cutoff -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem summable_weighted_totient_reciprocal_sq
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    Summable (fun q : ℕ => (q : ℝ)^(1/4 : ℝ)/(q.totient : ℝ)^2) := by
  have hbound := totient_reciprocal_subpower hMP (by norm_num : (0 : ℝ) < 1/8)
  have hmaj : Summable (fun q : ℕ => (q : ℝ)^(-(3/2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat hmaj
  filter_upwards [hbound,eventually_ge_atTop 1] with q hq hq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (q : ℝ)^(1/4 : ℝ)/(q.totient : ℝ)^2)]
  calc
    _ = (q : ℝ)^(1/4 : ℝ)*(1/(q.totient : ℝ))^2 := by ring
    _ ≤ (q : ℝ)^(1/4 : ℝ)*((q : ℝ)^(-1+(1/8 : ℝ)))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq 2) (by positivity)
    _ = _ := by rw [← Real.rpow_mul_natCast hq0.le,← Real.rpow_add hq0]; norm_num

theorem singularSeriesTail_power_bound
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ Q : ℕ, 0 < Q →
      singularSeriesTail Q ≤ A*(Q : ℝ)^(-(1/4 : ℝ)) := by
  let f := fun q : ℕ => (q : ℝ)^(1/4 : ℝ)/(q.totient : ℝ)^2
  have hf : Summable f := summable_weighted_totient_reciprocal_sq hMP
  refine ⟨∑' q, f q,tsum_nonneg (fun _ => by dsimp [f]; positivity),?_⟩
  intro Q hQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have htail : Summable (fun k : ℕ => 1/((k+Q).totient : ℝ)^2) :=
    (summable_totient_reciprocal_sq hMP).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hftail : Summable (fun k : ℕ => f (k+Q)) :=
    hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hmul : (Q : ℝ)^(1/4 : ℝ)*singularSeriesTail Q ≤ ∑' q, f q := by
    calc
      _ = ∑' k : ℕ, (Q : ℝ)^(1/4 : ℝ)*(1/((k+Q).totient : ℝ)^2) := by
        rw [tsum_mul_left]; rfl
      _ ≤ ∑' k : ℕ, f (k+Q) := by
        apply (htail.mul_left _).tsum_le_tsum _ hftail
        intro k
        dsimp [f]
        rw [div_eq_mul_inv,one_div]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Real.rpow_le_rpow hQr.le (by exact_mod_cast (Nat.le_add_left Q k)) (by norm_num)
      _ ≤ ∑' q, f q := by
        have he := hf.sum_add_tsum_nat_add Q
        have hp : 0 ≤ ∑ q ∈ range Q, f q := sum_nonneg (fun _ _ => by dsimp [f]; positivity)
        linarith
  have hdiv : singularSeriesTail Q ≤ (∑' q, f q) / (Q : ℝ)^(1/4 : ℝ) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hQr (1/4 : ℝ))).mpr
      ((_root_.mul_comm _ _).trans_le hmul)
  simpa only [Real.rpow_neg hQr.le,div_eq_mul_inv] using hdiv

theorem singularSeriesTail_uniform_vanishing
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j Q : ℕ, 0 < j → j ≤ B → (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ((j : ℝ)/j.totient)*singularSeriesTail (Q+1) ≤ ε B := by
  obtain ⟨A,hA,hpower⟩ := singularSeriesTail_power_bound hMP
  obtain ⟨K,hK,htotient⟩ := totient_log_bound hMP
  refine ⟨fun B => K*A*(Real.log B/(B : ℝ)^(1/10 : ℝ)),?_,?_⟩
  · have hlim := ((log_power_div_power_tendsto_zero 1 (by norm_num : (0 : ℝ) < 1/10)).const_mul
      (K*A)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def,Real.rpow_one,mul_zero] using hlim
  filter_upwards [htotient,eventually_ge_atTop 1] with B htot hB
  intro j Q hj hjB hQ
  have hBr : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hφ : (0 : ℝ) < j.totient := by exact_mod_cast Nat.totient_pos.mpr hj
  have hjpow : j ≤ B^15 := hjB.trans (le_self_pow₀ hB (by decide : 15 ≠ 0))
  have hratio : (j : ℝ)/j.totient ≤ K*Real.log B :=
    (div_le_iff₀ hφ).mpr (htot j hj hjpow)
  have hQ' : (B : ℝ)^(2/5 : ℝ) ≤ (Q+1 : ℕ) :=
    hQ.trans (by exact_mod_cast Nat.le_succ Q)
  have hdecay : ((Q+1 : ℕ) : ℝ)^(-(1/4 : ℝ)) ≤ (B : ℝ)^(-(1/10 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hBr (2/5 : ℝ)) hQ'
      (by norm_num : -(1/4 : ℝ) ≤ 0)
    rw [← Real.rpow_mul hBr.le] at hh
    norm_num at hh ⊢
    exact hh
  calc
    _ ≤ (K*Real.log B)*(A*((Q+1 : ℕ) : ℝ)^(-(1/4 : ℝ))) :=
      mul_le_mul hratio (hpower (Q+1) (by omega)) (singularSeriesTail_nonneg _)
        (mul_nonneg hK.le (Real.log_nonneg hB1))
    _ ≤ (K*Real.log B)*(A*(B : ℝ)^(-(1/10 : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay hA)
        (mul_nonneg hK.le (Real.log_nonneg hB1))
    _ = _ := by rw [Real.rpow_neg hBr.le]; ring

end JointDickman

end OAI
