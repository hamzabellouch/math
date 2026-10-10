import OAI.Combinatorics.BalancedRyser.Probability.ThinningTail
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw

namespace OAI

open scoped BigOperators Classical

namespace Balanced.SelectionThinning

noncomputable section
variable {V : Type*} [Fintype V]

theorem thinning_true_cylinder (rate : V → ℝ) (A : Finset V) :
    (∑ b : V → Bool, if ∀ v ∈ A, b v = true then thinningMass rate b else 0) =
      ∏ v ∈ A, rate v := by
  have hprod (b : V → Bool) :
      (if ∀ v ∈ A, b v = true then thinningMass rate b else 0) =
        ∏ v, bitMass (rate v) (b v) *
          (if v ∈ A then (if b v = true then 1 else 0) else 1) := by
    by_cases hb : ∀ v ∈ A, b v = true
    · rw [ite_eq_left hb]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ A
      · simp [hv, hb v hv]
      · simp [hv]
    · rw [ite_eq_right hb]
      obtain ⟨v, hv⟩ := not_forall.mp hb
      obtain ⟨hv, hflag⟩ := Classical.not_imp.mp hv
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [hv, hflag]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun v (b : Bool) =>
    bitMass (rate v) b * (if v ∈ A then (if b = true then 1 else 0) else 1))]
  have hsum (v : V) :
      (∑ b : Bool, bitMass (rate v) b *
        (if v ∈ A then (if b = true then 1 else 0) else 1)) =
      if v ∈ A then rate v else 1 := by
    by_cases hv : v ∈ A <;> simp [hv, bitMass]
  simp_rw [hsum]
  simp

theorem thinning_count_tail (rate : V → ℝ)
    (hrate : ∀ v, 0 ≤ rate v ∧ rate v ≤ 1) (A : Finset V) (k : ℕ) :
    (∑ b : V → Bool,
      if k ≤ (A.filter (fun v => b v = true)).card then thinningMass rate b else 0) ≤
      (∑ v ∈ A, rate v) ^ k / k.factorial := by
  have hm (b : V → Bool) := thinningMass_nonneg rate hrate b
  calc
    _ ≤ ∑ b : V → Bool, ∑ T ∈ A.powersetCard k,
        if ∀ v ∈ T, b v = true then thinningMass rate b else 0 := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : k ≤ (A.filter (fun v => b v = true)).card
      · rw [ite_eq_left hb]
        obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hb
        have hTA : T ∈ A.powersetCard k :=
          Finset.mem_powersetCard.mpr ⟨hT.trans (Finset.filter_subset _ _), hcard⟩
        have htrue : ∀ v ∈ T, b v = true := fun v hv =>
          (Finset.mem_filter.mp (hT hv)).2
        calc
          thinningMass rate b =
              (if ∀ v ∈ T, b v = true then thinningMass rate b else 0) := by
                rw [ite_eq_left htrue]
          _ ≤ _ := Finset.single_le_sum (s := A.powersetCard k)
            (f := fun T : Finset V => if ∀ v ∈ T, b v = true then thinningMass rate b else 0)
            (fun T _ => by split <;> first | exact hm b | exact le_rfl) hTA
      · rw [ite_eq_right hb]
        exact Finset.sum_nonneg (fun T _ => by split <;> first | exact hm b | exact le_rfl)
    _ = ∑ T ∈ A.powersetCard k, ∏ v ∈ T, rate v := by
      rw [Finset.sum_comm]
      simp_rw [thinning_true_cylinder]
    _ ≤ _ := Balanced.sum_prod_powersetCard_le A rate (fun v _ => (hrate v).1) k

end
end Balanced.SelectionThinning

namespace Balanced.Selection.Process

noncomputable section
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] [Fintype V] in

theorem thinned_inter_subset_true (G : Input I V) (S : State I V)
    (w : V) (flags : V → Bool) (A : Finset V) :
    thinned G S w flags ∩ A ⊆ A.filter (fun v => flags v = true) := by
  intro v hv
  rcases Finset.mem_inter.mp hv with ⟨hv, hA⟩
  exact Finset.mem_filter.mpr ⟨hA, (Finset.mem_filter.mp hv).2.2⟩

omit [Fintype I] in

theorem flags_thinned_tail_le (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S)
    (w : V) (A : Finset V) (m : ℝ)
    (hmean : ∑ v ∈ A, thinningRate p q G S v ≤ m) :
    (∑ flags : V → Bool,
      if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
      then flagsWeight p q G S flags else 0) ≤
      (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
        BernoulliTail.thinningCutoff (1 / 8) q := by
  let k := BernoulliTail.thinningCutoff (1 / 8) q
  have hrate (v : V) : 0 ≤ thinningRate p q G S v ∧ thinningRate p q G S v ≤ 1 := by
    have h := thinningRate_bounds_of_precheck p q t G S hpre v
    exact ⟨h.1, h.2.trans hpre.2.2.1.le⟩
  have hm : 0 ≤ m := (Finset.sum_nonneg (fun v _ => (hrate v).1)).trans hmean
  calc
    _ ≤ ∑ flags : V → Bool,
        if k ≤ (A.filter (fun v => flags v = true)).card then
          SelectionThinning.thinningMass (thinningRate p q G S) flags else 0 := by
      apply Finset.sum_le_sum
      intro flags _
      by_cases hf : (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
      · have hk : k ≤ (A.filter (fun v => flags v = true)).card := by
          have hsmall : k ≤ (thinned G S w flags ∩ A).card := by
            apply Nat.succ_le_iff.mpr
            exact (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg q) _)).mpr hf
          exact hsmall.trans (Finset.card_le_card (thinned_inter_subset_true G S w flags A))
        simp only [hf, ite_true, hk]
        rfl
      · rw [ite_eq_right hf]
        split
        · exact SelectionThinning.thinningMass_nonneg _ hrate flags
        · exact le_rfl
    _ ≤ (∑ v ∈ A, thinningRate p q G S v) ^ k / k.factorial :=
      SelectionThinning.thinning_count_tail _ hrate A k
    _ ≤ m ^ k / k.factorial := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun v _ => (hrate v).1)) hmean k
    _ ≤ _ := Balanced.pow_div_factorial_le_exp_ratio m hm k (by
      dsimp [k, BernoulliTail.thinningCutoff]
      omega)

theorem noise_thinned_tail_le (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S)
    (A : Finset V) (m : ℝ)
    (hmean : ∑ v ∈ A, thinningRate p q G S v ≤ m) :
    (∑ r : Noise I V,
      if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S r.2.1 r.2.2 ∩ A).card : ℝ)
      then noiseWeight p q G S r else 0) ≤
      (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
        BernoulliTail.thinningCutoff (1 / 8) q := by
  let ε := (Real.exp 1 * m / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
    BernoulliTail.thinningCutoff (1 / 8) q
  simp only [Noise, Fintype.sum_prod_type]
  calc
    _ = ∑ i : I, ∑ w : V, drawWeight G S i w *
        (∑ flags : V → Bool,
          if (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S w flags ∩ A).card : ℝ)
          then flagsWeight p q G S flags else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro flags _
      split <;> simp_all [noiseWeight]
    _ ≤ ∑ i : I, ∑ w : V, drawWeight G S i w * ε := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (flags_thinned_tail_le p q t G S hpre w A m hmean)
        (drawWeight_nonnegative G S i w)
    _ = ε := by
      simp_rw [← Finset.sum_mul]
      rw [sum_drawWeight G S hpre.1 (fun i hi => (hpre.2.2.2.1 i hi).1), one_mul]

end
end Balanced.Selection.Process

end OAI
