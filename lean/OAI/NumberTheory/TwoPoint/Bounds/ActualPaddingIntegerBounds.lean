import OAI.NumberTheory.TwoPoint.Bounds.PaddingActiveState
import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateComparison
import OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform

namespace OAI

/-! Truncated padding weights on actual integer intervals.  The finite
active-state comparison is used only after the degree restriction. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma uniformAverage_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] (f : (i : ι) → β i → ℝ) :
    uniformAverage (fun x : ∀ i, β i => ∏ i, f i (x i)) =
      ∏ i, uniformAverage (f i) := by
  simp only [uniformAverage, Fintype.card_pi, Nat.cast_prod]
  rw [← Fintype.prod_sum, prod_div_distrib]

lemma uniformAverage_padding_factor (p : ℕ) [NeZero p] (site : ℤ) :
    uniformAverage (fun z : ZMod p => if z + (site : ZMod p) = 0 then (5 : ℝ) else 1) =
      1 + 4 / (p : ℝ) := by
  have he (z : ZMod p) : z + (site : ZMod p) = 0 ↔ z = -(site : ZMod p) := by
    constructor <;> intro h <;> linear_combination h
  have hf (z : ZMod p) :
      (if z = -(site : ZMod p) then (5 : ℝ) else 1) =
        1 + if z = -(site : ZMod p) then (4 : ℝ) else 0 := by
    split_ifs <;> norm_num
  simp only [he, hf, uniformAverage, sum_add_distrib, sum_const,
    card_univ, nsmul_eq_mul, mul_one, sum_ite_eq', mem_univ, ite_true, ZMod.card]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

noncomputable def primeStateTruncatedWeight {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (M : ℕ) (site : ℤ) (z : ∀ i, ZMod (s i)) : ℝ :=
  let S := activeState (fun i => decide (z i + (site : ZMod (s i)) = 0))
  if S.card ≤ M then (5 : ℝ) ^ S.card else 0

lemma activeState_five_pow {m : ℕ} (x : BooleanCube m) :
    (5 : ℝ) ^ (activeState x).card = ∏ i, if x i then (5 : ℝ) else 1 := by
  rw [← prod_const]
  simp only [activeState, prod_filter]

lemma primeStateTruncatedWeight_average_le {m : ℕ} (s : Fin m → ℕ)
    [∀ i, NeZero (s i)] (M : ℕ) (site : ℤ) :
    uniformAverage (primeStateTruncatedWeight s M site) ≤
      ∏ i, (1 + 4 / (s i : ℝ)) := by
  calc
    _ ≤ uniformAverage (fun z : ∀ i, ZMod (s i) =>
        (5 : ℝ) ^ (activeState (fun i => decide (z i + (site : ZMod (s i)) = 0))).card) := by
      unfold uniformAverage
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro z _
      dsimp only [primeStateTruncatedWeight]
      split_ifs
      · exact le_rfl
      · positivity
    _ = uniformAverage (fun z : ∀ i, ZMod (s i) =>
        ∏ i, if z i + (site : ZMod (s i)) = 0 then (5 : ℝ) else 1) := by
      simp only [activeState_five_pow, decide_eq_true_eq]
    _ = _ := by
      rw [uniformAverage_pi_product
        (fun i (z : ZMod (s i)) => if z + (site : ZMod (s i)) = 0 then (5 : ℝ) else 1)]
      simp only [uniformAverage_padding_factor]

lemma padding_state_coefficient_bound (L : ℝ) (r : ℕ)
    (hL : 4800 ≤ L) (hr : (r : ℝ) ≤ 400 * Real.log L) :
    (5 : ℝ) ^ r ≤ Real.exp (L ^ 4) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hpow : 2000 * L ≤ L ^ 4 := by
    have h1 := mul_nonneg hL0 (show 0 ≤ L - 2000 by linarith)
    have h2 := mul_nonneg (sq_nonneg L) (show 0 ≤ L ^ 2 - 1 by nlinarith)
    nlinarith
  calc
    _ ≤ (Real.exp 5) ^ r := pow_le_pow_left₀ (by norm_num)
      (by linarith [Real.add_one_le_exp (5 : ℝ)]) r
    _ = Real.exp (r * 5) := by rw [Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem BravermanDepth22Input.eventually_prime_state_weight (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => primeStateTruncatedWeight s
        ⌊400 * Real.log L⌋₊ site (fun i => (a + x.val : ZMod (s i)))) ≤
          (∏ i, (1 + 4 / (s i : ℝ))) + Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hcompare⟩ := hBr.eventually_active_state_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hcompare, eventually_ge_atTop (4800 : ℝ)] with L hcompare hL
  intro m s _ hm hmL hcop hs site a N hN
  let M : ℕ := ⌊400 * Real.log L⌋₊
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hM : (M : ℝ) ≤ 400 * Real.log L := Nat.floor_le hlog
  let f : (Fin 1 → Finset (Fin m)) → ℝ := fun S => (5 : ℝ) ^ (S 0).card
  have hf : ∀ b : Fin 1 → boundedActiveStates m M,
      |f (fun r => (b r).val)| ≤ Real.exp (L ^ 4) := by
    intro b
    dsimp [f]
    rw [abs_of_nonneg (pow_nonneg (by norm_num) _)]
    apply padding_state_coefficient_bound L _ hL
    exact (Nat.cast_le.mpr (mem_boundedActiveStates.mp (b 0).property)).trans hM
  have hc := hcompare m s hm (by linarith) hcop hs 1 m m M hmL hM
    (by norm_num; linarith)
    (fun i => i) (fun i z => decide (z + (site : ZMod (s i)) = 0))
    (fun _ i => i) f hf a N hN
  have he (z : ∀ i, ZMod (s i)) :
      (if ∀ r : Fin 1,
        (activeState (fun i => residueCircuitInputs s (fun i => i)
          (fun i z => decide (z + (site : ZMod (s i)) = 0)) z i)).card ≤ M
        then f (fun _ => activeState (fun i => residueCircuitInputs s (fun i => i)
          (fun i z => decide (z + (site : ZMod (s i)) = 0)) z i)) else 0) =
      primeStateTruncatedWeight s M site z := by
    simp only [residueCircuitInputs, f, primeStateTruncatedWeight, forall_const]
  dsimp only at hc
  simp only [he] at hc
  have hb := primeStateTruncatedWeight_average_le s M site
  linarith [(le_abs_self
    (uniformAverage (fun x : Fin N => primeStateTruncatedWeight s M site
      (fun i => (a + x.val : ZMod (s i)))) -
        uniformAverage (primeStateTruncatedWeight s M site))).trans hc]

lemma primeStateTruncatedWeight_actual {m : ℕ} (Q : Finset ℕ) (e : Fin m ≃ Q)
    [∀ i, NeZero (e i).val] (M : ℕ) (site n : ℤ) :
    primeStateTruncatedWeight (fun i => (e i).val) M site
      (fun i => (n : ZMod (e i).val)) =
      if actualPaddingDegree Q (n + site) ≤ M then actualPaddingWeight Q (n + site) else 0 := by
  have hs : activeState (fun i => decide ((n : ZMod (e i).val) +
      (site : ZMod (e i).val) = 0)) = paddingActiveState Q e (n + site) := by
    apply (paddingActiveState_residue Q e _ (n + site) _).symm
    intro i
    exact Int.cast_add n site
  simp only [primeStateTruncatedWeight, hs, paddingActiveState_card, actualPaddingWeight]

lemma primeSet_card_le_exp (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (L : ℝ) (hupper : ∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) :
    (Q.card : ℝ) ≤ Real.exp L := by
  have hs : Q ⊆ Icc 1 ⌊Real.exp L⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(hQ p hp).one_lt.le,
      (Nat.le_floor_iff (Real.exp_pos L).le).mpr (hupper p hp)⟩
  have hc : Q.card ≤ ⌊Real.exp L⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hs
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.exp_pos L).le)

lemma paddingTiltNormalizer_one_le (Q : Finset ℕ) : 1 ≤ paddingTiltNormalizer Q := by
  calc
    1 = ∏ _p : Q, (1 : ℝ) := by simp
    _ ≤ paddingTiltNormalizer Q := by
      apply prod_le_prod₀
      · intro p _
        exact zero_le_one
      · intro p _
        exact le_add_of_nonneg_right (by positivity)

/-- The manuscript's truncated-weight estimate, for literal integer
sites and every permitted interval and offset. -/
theorem BravermanDepth22Input.eventually_actual_padding_weight (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let T := uniformAverage (fun x : Fin N =>
        (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
          if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site) then 1 else 0)
      T ≤ paddingTiltNormalizer Q + Real.exp (-(L ^ 9)) ∧
        T ≤ 2 * paddingTiltNormalizer Q := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_prime_state_weight
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (4800 : ℝ)] with L hb hL
  intro Q hQ hupper site a N hN
  have hL0 : 0 ≤ L := by linarith
  have hlog : 0 ≤ 400 * Real.log L :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have hmain : uniformAverage (fun x : Fin N =>
      (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
        if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site) then 1 else 0) ≤
      paddingTiltNormalizer Q + Real.exp (-(L ^ 9)) := by
    by_cases hne : Q.Nonempty
    · let m := Fintype.card Q
      let e : Fin m ≃ Q := (Fintype.equivFin Q).symm
      let s := fun i : Fin m => (e i).val
      let (i : Fin m) : NeZero (s i) := ⟨(hQ _ (e i).property).ne_zero⟩
      have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨hne.choose, hne.choose_spec⟩⟩
      have hmL : (m : ℝ) ≤ Real.exp L := by
        simpa only [m, Fintype.card_coe] using primeSet_card_le_exp Q hQ L hupper
      have hcop : Pairwise (fun i j => (s i).Coprime (s j)) := by
        intro i j hij
        apply (Nat.coprime_primes (hQ _ (e i).property) (hQ _ (e j).property)).mpr
        intro he
        exact hij (e.injective (Subtype.ext he))
      have hs (i : Fin m) : (s i : ℝ) ≤ Real.exp L := hupper _ (e i).property
      have hh := hb m s hm hmL hcop hs site a N hN
      have heval (x : Fin N) : primeStateTruncatedWeight s ⌊400 * Real.log L⌋₊ site
          (fun i => (a + x.val : ZMod (s i))) =
          (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
            if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site) then 1 else 0 := by
        have hx := primeStateTruncatedWeight_actual Q e ⌊400 * Real.log L⌋₊ site
          ((a + x.val : ℕ) : ℤ)
        simp only [Nat.cast_add, Int.cast_add, Int.cast_natCast] at hx
        rw [hx]
        simp only [Nat.le_floor_iff hlog, actualPaddingVertex_sq,
          actualPaddingDegreeCut, Nat.cast_add]
        split_ifs <;> simp
      have hnorm : (∏ i, (1 + 4 / (s i : ℝ))) = paddingTiltNormalizer Q :=
        e.prod_comp (fun p : Q => 1 + 4 / (p.val : ℝ))
      simpa only [heval, hnorm] using hh
    · have hQempty : Q = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst Q
      have hNpos : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
      let : NeZero N := ⟨by omega⟩
      have hf (x : Fin N) :
          (actualPaddingVertex ∅ (((a + x.val : ℕ) : ℤ) + site)) ^ 2 *
            (if actualPaddingDegreeCut ∅ L (((a + x.val : ℕ) : ℤ) + site)
              then (1 : ℝ) else 0) = 1 := by
        simp only [actualPaddingVertex_sq, actualPaddingWeight, actualPaddingDegree,
          filter_empty, card_empty, pow_zero, actualPaddingDegreeCut, Nat.cast_zero,
          hlog, ite_true, mul_one]
      simp only [hf, uniformAverage_const]
      have hnorm : paddingTiltNormalizer ∅ = 1 := by simp [paddingTiltNormalizer]
      rw [hnorm]
      linarith [Real.exp_pos (-(L ^ 9))]
  dsimp only
  refine ⟨hmain, ?_⟩
  have he : Real.exp (-(L ^ 9)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg hL0 _))
  have hS := paddingTiltNormalizer_one_le Q
  linarith

/-- Summing over any fixed finite collection of offsets costs its cardinality. -/
theorem BravermanDepth22Input.eventually_actual_padding_weight_sum
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Q : Finset ℕ), (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, (p : ℝ) ≤ Real.exp L) →
      ∀ {ι : Type*} [DecidableEq ι] (offsets : Finset ι) (site : ι → ℤ)
        (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      (∑ i ∈ offsets, uniformAverage (fun x : Fin N =>
        (actualPaddingVertex Q (((a + x.val : ℕ) : ℤ) + site i)) ^ 2 *
          if actualPaddingDegreeCut Q L (((a + x.val : ℕ) : ℤ) + site i)
            then 1 else 0)) ≤
        2 * (offsets.card : ℝ) * paddingTiltNormalizer Q := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_actual_padding_weight
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro Q hQ hupper ι _ offsets site a N hN
  calc
    _ ≤ ∑ _i ∈ offsets, 2 * paddingTiltNormalizer Q := by
      apply sum_le_sum
      intro i _
      exact (hb Q hQ hupper (site i) a N hN).2
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI
