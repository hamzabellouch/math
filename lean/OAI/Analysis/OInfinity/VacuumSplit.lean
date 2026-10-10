import OAI.Analysis.OInfinity.FiniteRowCompletion

namespace OAI

/-! # A concrete almost central split of a canonical finite O∞ row

The corner and its coisometric row are constructed from unused canonical
isometries and the finite word sum. Its complement is the range of an actual
isometry. Thus the vacuum compression and the complement are both controlled
without assuming a projection-classification theorem.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma transported_row {J : Type*} [Fintype J] [DecidableEq J]
    (v q : E) (t : J → E) (hv : star v * v = q) (hvq : v * q = v)
    (htl : ∀ i, q * t i = t i) (htr : ∀ i, t i * q = t i)
    (htt : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (ht : ∑ i, t i * star (t i) = q) :
    (∀ i j, star (v * t i * star v) * (v * t j * star v) =
      if i = j then v * star v else 0) ∧
    (∑ i, (v * t i * star v) * star (v * t i * star v)) = v * star v := by
  constructor
  · intro i j
    calc
      _ = v * star (t i) * (star v * v) * t j * star v := by
        simp only [star_mul, star_star]
        noncomm_ring
      _ = v * (star (t i) * t j) * star v := by rw [hv, mul_assoc (v * star (t i)), htl]; noncomm_ring
      _ = _ := by rw [htt]; split_ifs <;> simp only [hvq, mul_zero, zero_mul]
  · have he (i : J) : (v * t i * star v) * star (v * t i * star v) =
        v * (t i * star (t i)) * star v := by
      simp only [star_mul, star_star]
      calc
        _ = v * (t i * q) * star (t i) * star v := by
          rw [← hv]; noncomm_ring
        _ = _ := by rw [htr]; noncomm_ring
    simp only [he, ← Finset.mul_sum, ← Finset.sum_mul, ht, hvq]

private lemma transported_zeroCornerRow (q a b v : E)
    (hqq : q * q = q) (hqa : q * a = a) (hqb : q * b = b) (hbq : b * q = b)
    (hvg : star v * v = q) (hvq : v * q = v) :
    ∀ n i, v * zeroCornerRow q a b n i * star v =
      zeroCornerRow (v * star v) (v * a * star v) (v * b * star v) n i := by
  intro n
  induction n with
  | zero => intro i; change v * q * star v = v * star v; rw [hvq]
  | succ n ih =>
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change v * (a * zeroCornerRow q a b n j) * star v =
      (v * a * star v) * zeroCornerRow (v * star v) (v * a * star v) (v * b * star v) n j
    rw [← ih j]
    calc
      _ = v * a * (q * zeroCornerRow q a b n j) * star v := by
        rw [(zeroCornerRow_support q a b hqq hqa hqb hbq n j).1]
        noncomm_ring
      _ = _ := by rw [← hvg]; noncomm_ring

/-- The explicit finite split, retaining its transported binary generators. -/
lemma exists_canonical_vacuum_split_with_pair_and_isometry [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f w : E) (g : Fin (n + 1) → E),
      f ≠ 0 ∧ star f = f ∧ f * f = f ∧
      star w * w = 1 ∧ w * star w = 1 - f ∧
      (∀ i j, star (g i) * g j = if i = j then f else 0) ∧
      (∑ i, g i * star (g i)) = f ∧
      (∀ i : Fin (n + 1), ‖s i * f - f * s i‖ < ε) ∧
      (∀ i : Fin (n + 1), ‖f * s i * f - g i‖ < ε) ∧
      ‖f * (1 - ∑ i : Fin (n + 1), s i * star (s i)) * f‖ < ε ∧
      f * s (n + 2) = 0 ∧
      ∃ A B : E, star A * A = f ∧ star B * B = f ∧ star A * B = 0 ∧
        A * star A + B * star B = f ∧
        (∀ i, g i = zeroCornerRow f A B n i) ∧
        ∃ z : E, star z * z = 1 ∧ f * z = z := by
  let z := s (n + 2)
  let r := s (n + 1)
  let q := 1 - z * star z
  have hz : star z * z = 1 := by simpa only [z, ite_true] using hs (n + 2) (n + 2)
  have hrr : star r * r = 1 := by simpa only [r, ite_true] using hs (n + 1) (n + 1)
  have hqstar : star q = q := by simp only [q, star_sub, star_one, star_mul, star_star]
  have hqq : q * q = q := by
    have hzz : (z * star z) * (z * star z) = z * star z := by
      calc
        _ = z * (star z * z) * star z := by noncomm_ring
        _ = _ := by rw [hz, mul_one]
    dsimp only [q]
    noncomm_ring [hzz]
  have hz₁ : star z * s (n + 3) = 0 := by simp only [z, hs, show n + 2 ≠ n + 3 by omega, ite_false]
  have hz₂ : star z * s (n + 4) = 0 := by simp only [z, hs, show n + 2 ≠ n + 4 by omega, ite_false]
  have h₁₂ : star (s (n + 3)) * s (n + 4) = 0 := by simp only [hs, show n + 3 ≠ n + 4 by omega, ite_false]
  obtain ⟨a, b, u₀, _hu₀, _ha, _hb, _hu₀eq, haa, hbb, hab, habsum⟩ :=
    exists_zero_corner_cuntz_pair z (s (n + 3)) (s (n + 4)) hz
      (by simpa using hs (n + 3) (n + 3)) (by simpa using hs (n + 4) (n + 4))
      hz₁ hz₂ h₁₂
  change star a * a = q at haa
  change star b * b = q at hbb
  change a * star a + b * star b = q at habsum
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab habsum
  let t := zeroCornerRow q a b n
  have htl (i : Fin (n + 1)) : q * t i = t i := (zeroCornerRow_support q a b hqq hqa hqb hbq n i).1
  have htr (i : Fin (n + 1)) : t i * q = t i := (zeroCornerRow_support q a b hqq hqa hqb hbq n i).2
  have htt : ∀ i j, star (t i) * t j = if i = j then q else 0 :=
    zeroCornerRow_gram q a b hqstar hqq haa hbb hab hqa hqb hbq n
  have ht : ∑ i, t i * star (t i) = q := zeroCornerRow_range_sum q a b hqstar hqq haq habsum n
  let s' (i : Fin (n + 1)) := s i
  have hs' (i j : Fin (n + 1)) : star (s' i) * s' j = if i = j then 1 else 0 := by
    simpa only [s', Fin.ext_iff] using hs i j
  have hri (i : Fin (n + 1)) : star r * s' i = 0 := by
    change star (s (n + 1)) * s i = 0
    rw [hs, ite_eq_right (by omega)]
  have hzi (i : Fin (n + 1)) : star z * s' i = 0 := by
    change star (s (n + 2)) * s i = 0
    rw [hs, ite_eq_right (by omega)]
  have hzr : star z * r = 0 := by simp only [z, r, hs, show n + 2 ≠ n + 1 by omega, ite_false]
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < min ε ((ε / 4) ^ 2) by positivity)
  have hmε : ((m : ℝ) + 1)⁻¹ < ε := by simpa only [one_div] using hm.trans_le (min_le_left _ _)
  have hmSq : ((m : ℝ) + 1)⁻¹ < (ε / 4) ^ 2 := by simpa only [one_div] using hm.trans_le (min_le_right _ _)
  let v := finiteRowIsometry s' t r q m
  let f := finiteRowRange s' t r q m
  have hvg : star v * v = q := finiteRowIsometry_gram s' t r q hqq hqstar hrr hri hs' htr ht m
  have hvq : v * q = v := relativeIsometry_mul_support v q hvg hqstar hqq
  have hfv : f * v = v := by change (v * star v) * v = v; rw [mul_assoc, hvg, hvq]
  obtain ⟨u, _hu, _hueq, _huq, huw, hwrange⟩ :=
    exists_connected_finiteRowCompletion s' t r q z hqq hqstar hrr hri hs' htr ht hz hzr hzi rfl m
  let g (i : Fin (n + 1)) := v * t i * star v
  have hg := transported_row v q t hvg hvq htl htr htt ht
  have hqne : q ≠ 0 := by
    intro hq0
    have hqa₁ : q * s (n + 3) = s (n + 3) := by
      dsimp only [q]
      rw [sub_mul, one_mul, mul_assoc, hz₁, mul_zero, sub_zero]
    rw [hq0, zero_mul] at hqa₁
    have hx := hs (n + 3) (n + 3)
    rw [← hqa₁, star_zero, zero_mul, ite_eq_left rfl] at hx
    exact zero_ne_one hx
  refine ⟨f, (u : E) * z, g, ?_, finiteRowRange_star s' t r q m,
    finiteRowRange_sq s' t r q hqq hqstar hrr hri hs' htr ht m, huw, hwrange,
    hg.1, hg.2, ?_, ?_, ?_, ?_⟩
  · intro hf
    have hv0 : v = 0 := by rw [← hfv, hf, zero_mul]
    have hq0 : q = 0 := by rw [← hvg, hv0, star_zero, zero_mul]
    exact hqne hq0
  · intro i
    have hbound := finiteRowRange_commutator_bound s' t r q hqq hqstar hrr hri hs' htr ht htt m i
    have hsqrt₁ := Real.sq_sqrt (show 0 ≤ ((m : ℝ) + 1)⁻¹ by positivity)
    have hsqrt₂ := Real.sq_sqrt (show 0 ≤ 2 / ((m : ℝ) + 1) by positivity)
    have hc : 2 / ((m : ℝ) + 1) = 2 * ((m : ℝ) + 1)⁻¹ := by rw [div_eq_mul_inv]
    have h₁ : Real.sqrt (((m : ℝ) + 1)⁻¹) < ε / 4 := by nlinarith [Real.sqrt_nonneg (((m : ℝ) + 1)⁻¹)]
    have h₂ : Real.sqrt (2 / ((m : ℝ) + 1)) < ε / 2 := by
      have hsqrt₂' := hsqrt₂.trans hc
      nlinarith [Real.sqrt_nonneg (2 / ((m : ℝ) + 1))]
    exact hbound.trans_lt (by linarith)
  · intro i
    have hcomp : f * s i * f = (((m : ℝ) / ((m : ℝ) + 1) : ℝ) : ℂ) • g i := by
      calc
        _ = v * (star v * s' i * v) * star v := by change (v * star v) * s' i * (v * star v) = _; noncomm_ring
        _ = _ := by
          rw [finiteRowIsometry_compression s' t r q hqq hqstar hrr hri hs' htr ht m i,
            mul_smul_comm, smul_mul_assoc]
    have hgn : ‖g i‖ ≤ 1 := by
      have he := congrArg norm (hg.1 i i)
      simp only [ite_true, CStarRing.norm_star_mul_self] at he
      change ‖g i‖ * ‖g i‖ = ‖f‖ at he
      have hfn : ‖f‖ ≤ 1 := IsStarProjection.norm_le _ (isStarProjection_iff'.mpr
        ⟨finiteRowRange_sq s' t r q hqq hqstar hrr hri hs' htr ht m, finiteRowRange_star s' t r q m⟩)
      nlinarith [norm_nonneg (g i)]
    have he : f * s i * f - g i = -(((((m : ℝ) + 1)⁻¹ : ℝ) : ℂ) • g i) := by
      rw [hcomp]
      have hc : ((m : ℝ) / ((m : ℝ) + 1)) - 1 = -((m : ℝ) + 1)⁻¹ := by
        have hn : (m : ℝ) + 1 ≠ 0 := by positivity
        field_simp
        ring
      calc
        _ = (((m : ℝ) / ((m : ℝ) + 1) - 1 : ℝ) : ℂ) • g i := by push_cast; module
        _ = _ := by rw [hc, Complex.ofReal_neg, neg_smul]
    rw [he, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ ((m : ℝ) + 1)⁻¹)]
    exact (mul_le_of_le_one_right (by positivity) hgn).trans_lt hmε
  · exact (finiteRowRange_vacuum_norm s' t r q hqq hqstar hrr hri hs' htr ht m).trans_lt hmε
  · refine ⟨finiteRowRange_unused s' t r q z hzr hzi m, ?_⟩
    let pair : Fin 2 → E := ![a, b]
    have hba : star b * a = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star hab
    have hpl (i : Fin 2) : q * pair i = pair i := by
      fin_cases i
      · exact hqa
      · exact hqb
    have hpr (i : Fin 2) : pair i * q = pair i := by
      fin_cases i
      · exact haq
      · exact hbq
    have hpg (i j : Fin 2) : star (pair i) * pair j = if i = j then q else 0 := by
      fin_cases i <;> fin_cases j <;> simp [pair, haa, hbb, hab, hba]
    have hps : ∑ i, pair i * star (pair i) = q := by
      simpa only [Fin.sum_univ_two, pair, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using habsum
    have hpair := transported_row v q pair hvg hvq hpl hpr hpg hps
    have hvf : v * star v = f := rfl
    refine ⟨v * a * star v, v * b * star v, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [pair, Matrix.cons_val_zero, ite_true, hvf] using hpair.1 0 0
    · simpa only [pair, Matrix.cons_val_one, Matrix.cons_val_fin_one, ite_true, hvf] using hpair.1 1 1
    · simpa only [pair, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Fin.zero_ne_one, ite_false] using hpair.1 0 1
    · simpa only [Fin.sum_univ_two, pair, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, hvf] using hpair.2
    · intro i
      exact transported_zeroCornerRow q a b v hqq hqa hqb hbq hvg hvq n i
    · have hqz : q * s (n + 3) = s (n + 3) := by
        dsimp only [q]
        rw [sub_mul, one_mul, mul_assoc, hz₁, mul_zero, sub_zero]
      refine ⟨v * s (n + 3), ?_, ?_⟩
      · rw [star_mul]
        calc
          _ = star (s (n + 3)) * (star v * v) * s (n + 3) := by noncomm_ring
          _ = 1 := by
            rw [hvg, mul_assoc, hqz]
            simpa only [ite_true] using hs (n + 3) (n + 3)
      · rw [← mul_assoc, hfv]

/-- The explicit finite split, retaining its transported binary generators. -/
lemma exists_canonical_vacuum_split_with_pair [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f w : E) (g : Fin (n + 1) → E),
      f ≠ 0 ∧ star f = f ∧ f * f = f ∧
      star w * w = 1 ∧ w * star w = 1 - f ∧
      (∀ i j, star (g i) * g j = if i = j then f else 0) ∧
      (∑ i, g i * star (g i)) = f ∧
      (∀ i : Fin (n + 1), ‖s i * f - f * s i‖ < ε) ∧
      (∀ i : Fin (n + 1), ‖f * s i * f - g i‖ < ε) ∧
      ‖f * (1 - ∑ i : Fin (n + 1), s i * star (s i)) * f‖ < ε ∧
      f * s (n + 2) = 0 ∧
      ∃ A B : E, star A * A = f ∧ star B * B = f ∧ star A * B = 0 ∧
        A * star A + B * star B = f ∧
        ∀ i, g i = zeroCornerRow f A B n i := by
  obtain ⟨f, w, g, hf, hfs, hff, hw, hwr, hg, hgs, hc, hfg, hfv, hfz,
    A, B, hA, hB, hAB, hsum, he, _hz⟩ :=
    exists_canonical_vacuum_split_with_pair_and_isometry s hs n ε hε
  exact ⟨f, w, g, hf, hfs, hff, hw, hwr, hg, hgs, hc, hfg, hfv, hfz,
    A, B, hA, hB, hAB, hsum, he⟩

/-- Every finite canonical row admits the explicit vacuum-killing split.
The returned row is coisometric in `f`, and an actual isometry fills `1-f`. -/
lemma exists_canonical_vacuum_split [Nontrivial E] (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f w : E) (g : Fin (n + 1) → E),
      f ≠ 0 ∧ star f = f ∧ f * f = f ∧
      star w * w = 1 ∧ w * star w = 1 - f ∧
      (∀ i j, star (g i) * g j = if i = j then f else 0) ∧
      (∑ i, g i * star (g i)) = f ∧
      (∀ i : Fin (n + 1), ‖s i * f - f * s i‖ < ε) ∧
      (∀ i : Fin (n + 1), ‖f * s i * f - g i‖ < ε) ∧
      ‖f * (1 - ∑ i : Fin (n + 1), s i * star (s i)) * f‖ < ε ∧
      f * s (n + 2) = 0 := by
  obtain ⟨f, w, g, hf, hfs, hff, hw, hwr, hg, hgs, hc, hfg, hfv, hfz, _hp⟩ :=
    exists_canonical_vacuum_split_with_pair s hs n ε hε
  exact ⟨f, w, g, hf, hfs, hff, hw, hwr, hg, hgs, hc, hfg, hfv, hfz⟩

end WeakPureInfiniteness

end

end OAI
