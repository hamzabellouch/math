import Mathlib

namespace OAI

/-! Signature. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
open QuadraticMap

namespace Contingency

 

section Signature
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

 

theorem sigPos_le_one_of_kernel (Q : QuadraticForm ℝ V) (l : V →ₗ[ℝ] ℝ)
    (h : ∀ x, l x = 0 → Q x ≤ 0) : sigPos Q ≤ 1 := by
  have hs := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := Q) (V := LinearMap.ker l) (fun x hx => h x hx)
  have hd := l.finrank_range_add_finrank_ker
  have hr := (LinearMap.range l).finrank_le
  simp only [Module.finrank_self] at hr
  omega

 
omit [FiniteDimensional ℝ V] in
theorem quadratic_add (Q : QuadraticForm ℝ V) (x y : V) :
    Q (x + y) = Q x + Q y + 2 * Q.associated x y := by
  have h := Q.associated_apply ℝ x y
  norm_num at h
  linarith

 

theorem sigPos_two_of_orthogonal_positive (Q : QuadraticForm ℝ V) (e v : V)
    (he : 0 < Q e) (hv : 0 < Q v) (hev : Q.associated e v = 0) :
    2 ≤ sigPos Q := by
  let f : (ℝ × ℝ) →ₗ[ℝ] V :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight e + (LinearMap.snd ℝ ℝ ℝ).smulRight v
  have hf (p : ℝ × ℝ) : Q (f p) = p.1 ^ 2 * Q e + p.2 ^ 2 * Q v := by
    change Q (p.1 • e + p.2 • v) = _
    rw [quadratic_add]
    simp [QuadraticMap.map_smul, map_smul, hev, pow_two]
  have hpos (p : ℝ × ℝ) (hp : p ≠ 0) : 0 < Q (f p) := by
    rw [hf]
    have hp' : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hp
      exact Prod.ext h.1 h.2
    rcases hp' with hp' | hp'
    · exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_ne_zero hp') he)
        (mul_nonneg (sq_nonneg _) hv.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) he.le)
        (mul_pos (sq_pos_of_ne_zero hp') hv)
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    by_contra hp'
    have := hpos p hp'
    rw [hp, QuadraticMap.map_zero] at this
    exact lt_irrefl _ this
  have hdef : (Q.restrict (LinearMap.range f)).PosDef := by
    rintro ⟨x, hx⟩ hne
    obtain ⟨p, rfl⟩ := hx
    apply hpos
    intro hp
    apply hne
    apply Subtype.ext
    simp [hp]
  have hs := le_sigPos_of_posDef Q hdef
  have hr := LinearEquiv.finrank_eq (LinearEquiv.ofInjective f hinj)
  have htwo : Module.finrank ℝ (LinearMap.range f) = 2 := by
    rw [← hr]
    simp [Module.finrank_prod]
  rwa [htwo] at hs

 
theorem positive_projection (Q : QuadraticForm ℝ V) (hs : sigPos Q ≤ 1)
    (e v : V) (he : 0 < Q e) :
    Q v ≤ (Q.associated v e) ^ 2 / Q e := by
  let a := Q.associated v e / Q e
  let w := v - a • e
  have hee : Q.associated e e = Q e := Q.associated_eq_self_apply ℝ e
  have hew : Q.associated e w = 0 := by
    simp only [w, map_sub, map_smul]
    rw [QuadraticMap.associated_isSymm ℝ Q e v, hee]
    simp [a, div_mul_cancel₀ _ he.ne']
  have hw : Q w ≤ 0 := by
    by_contra h
    have := sigPos_two_of_orthogonal_positive Q e w he (lt_of_not_ge h) hew
    omega
  have hexp : Q w = Q v - 2 * a * Q.associated v e + a ^ 2 * Q e := by
    rw [show w = v + (-a) • e by simp [w, sub_eq_add_neg], quadratic_add]
    simp only [QuadraticMap.map_smul, map_smul, smul_eq_mul]
    ring
  rw [hexp] at hw
  dsimp [a] at hw
  field_simp at hw ⊢
  nlinarith [sq_pos_of_pos he]

 
noncomputable def pairForm (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) : QuadraticForm ℝ (V × ℝ × ℝ) :=
  let old := LinearMap.fst ℝ V (ℝ × ℝ)
  let x := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ V (ℝ × ℝ))
  let y := (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ V (ℝ × ℝ))
  Q.comp old + 2 • linMulLin (Sa.comp old) x + 2 • linMulLin (Sb.comp old) y +
    a • linMulLin x x + (2 * b) • linMulLin x y + c • linMulLin y y

omit [FiniteDimensional ℝ V] in
theorem pairForm_apply (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) (h : V) (x y : ℝ) :
    pairForm Q Sa Sb a b c (h, x, y) =
      Q h + 2 * Sa h * x + 2 * Sb h * y + a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  simp [pairForm, linMulLin_apply, pow_two, mul_assoc]

omit [FiniteDimensional ℝ V] in
theorem pairForm_first (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) : pairForm Q Sa Sb a b c (0, 1, 0) = a := by
  simp [pairForm_apply]

omit [FiniteDimensional ℝ V] in
theorem pairForm_second (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) : pairForm Q Sa Sb a b c (0, 0, 1) = c := by
  simp [pairForm_apply]

omit [FiniteDimensional ℝ V] in
theorem pairForm_both (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) : pairForm Q Sa Sb a b c (0, 1, 1) = a + 2 * b + c := by
  simp [pairForm_apply]

omit [FiniteDimensional ℝ V] in
theorem pairForm_associated_first (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) (h : V) (x y : ℝ) :
    (pairForm Q Sa Sb a b c).associated (h, x, y) (0, 1, 0) =
      Sa h + a * x + b * y := by
  rw [QuadraticMap.associated_apply]
  simp [pairForm_apply]
  ring

omit [FiniteDimensional ℝ V] in
theorem pairForm_associated_second (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) (h : V) (x y : ℝ) :
    (pairForm Q Sa Sb a b c).associated (h, x, y) (0, 0, 1) =
      Sb h + b * x + c * y := by
  rw [QuadraticMap.associated_apply]
  simp [pairForm_apply]
  ring

 

theorem pair_one (Q : QuadraticForm ℝ V) (Sa Sb : V →ₗ[ℝ] ℝ)
    (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hpositive : 0 < a ∨ 0 < c ∨ 0 < b)
    (hs : sigPos (pairForm Q Sa Sb a b c) ≤ 1)
    (h : V) (gp g gn : ℝ)
    (hSa : Sa h = b * g - a * gp) (hSb : Sb h = c * gn - b * g) :
    2 * b * g ^ 2 - a * gp ^ 2 - c * gn ^ 2 ≤ -Q h := by
  let M := pairForm Q Sa Sb a b c
  have hfirst : M.associated (h, g, -g) (0, 1, 0) = a * (g - gp) := by
    rw [pairForm_associated_first, hSa]
    ring
  have hsecond : M.associated (h, g, -g) (0, 0, 1) = c * (gn - g) := by
    rw [pairForm_associated_second, hSb]
    ring
  have hbound : M (h, g, -g) ≤ a * (g - gp) ^ 2 + c * (g - gn) ^ 2 := by
    by_cases ha' : 0 < a
    · have ht := positive_projection M hs (0, 1, 0) (h, g, -g)
        (by simpa [M, pairForm_first] using ha')
      rw [hfirst, pairForm_first] at ht
      have heq : (a * (g - gp)) ^ 2 / a = a * (g - gp) ^ 2 := by
        field_simp
      rw [heq] at ht
      exact ht.trans (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _)))
    · by_cases hc' : 0 < c
      · have ht := positive_projection M hs (0, 0, 1) (h, g, -g)
          (by simpa [M, pairForm_second] using hc')
        rw [hsecond, pairForm_second] at ht
        have heq : (c * (gn - g)) ^ 2 / c = c * (g - gn) ^ 2 := by
          field_simp
          ring
        rw [heq] at ht
        exact ht.trans (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))
      · have hae : a = 0 := le_antisymm (le_of_not_gt ha') ha
        have hce : c = 0 := le_antisymm (le_of_not_gt hc') hc
        have hb : 0 < b := hpositive.resolve_left ha' |>.resolve_left hc'
        have ht := positive_projection M hs (0, 1, 1) (h, g, -g)
          (by rw [pairForm_both, hae, hce]; linarith)
        have heq : M.associated (h, g, -g) (0, 1, 1) = 0 := by
          have hsum : ((0 : V), (1 : ℝ), (1 : ℝ)) = (0, 1, 0) + (0, 0, 1) := by
            ext <;> simp
          rw [hsum, map_add, hfirst, hsecond, hae, hce]
          ring
        simpa [heq, hae, hce] using ht
  rw [pairForm_apply, hSa, hSb] at hbound
  nlinarith

 
noncomputable def pairCumulative (D : ℕ) (u : ℕ → ℝ) (S : ℕ → V →ₗ[ℝ] ℝ)
    (h : V) (j : ℕ) : ℝ :=
  if 0 < j ∧ j < D then (∑ l ∈ Finset.range j, S l h) / u j else 0

omit [FiniteDimensional ℝ V] in
theorem pairCumulative_mul (D : ℕ) (u : ℕ → ℝ) (S : ℕ → V →ₗ[ℝ] ℝ)
    (hu : ∀ j, 0 < j → j < D → 0 < u j) (h : V)
    (hbal : ∑ l ∈ Finset.range D, S l h = 0) (j : ℕ) (hj : j ≤ D) :
    u j * pairCumulative D u S h j = ∑ l ∈ Finset.range j, S l h := by
  by_cases h0 : j = 0
  · simp [h0, pairCumulative]
  by_cases hD : j = D
  · simp [hD, pairCumulative, hbal]
  have hj' : 0 < j ∧ j < D := by omega
  simp only [pairCumulative, ite_eq_left hj']
  exact mul_div_cancel₀ _ (hu j hj'.1 hj'.2).ne'

 
omit [FiniteDimensional ℝ V] in
theorem pairCumulative_difference (D : ℕ) (u : ℕ → ℝ) (S : ℕ → V →ₗ[ℝ] ℝ)
    (hu : ∀ j, 0 < j → j < D → 0 < u j) (h : V)
    (hbal : ∑ l ∈ Finset.range D, S l h = 0) (j : ℕ) (hj : j < D) :
    S j h = u (j+1) * pairCumulative D u S h (j+1) -
      u j * pairCumulative D u S h j := by
  rw [pairCumulative_mul D u S hu h hbal _ (by omega),
    pairCumulative_mul D u S hu h hbal _ (by omega), Finset.sum_range_succ]
  ring

 
noncomputable def pairPrevious (S : ℕ → V →ₗ[ℝ] ℝ) (j : ℕ) : V →ₗ[ℝ] ℝ :=
  if j = 0 then 0 else S (j-1)

 

theorem pair_sequence_one (D : ℕ) (hD : 2 ≤ D) (u : ℕ → ℝ)
    (S : ℕ → V →ₗ[ℝ] ℝ) (Q : ℕ → QuadraticForm ℝ V)
    (hu : ∀ j, 0 < j → j < D → 0 < u j)
    (uzero : ∀ j, j = 0 ∨ D ≤ j → u j = 0) (sD : S D = 0)
    (h : V) (hbal : ∑ l ∈ Finset.range D, S l h = 0)
    (j : ℕ) (hj : j ≤ D)
    (hs : sigPos (pairForm (Q j) (pairPrevious S j) (S j)
      (u (j-1)) (u j) (u (j+1))) ≤ 1) :
    2 * u j * pairCumulative D u S h j ^ 2 -
        u (j-1) * pairCumulative D u S h (j-1) ^ 2 -
        u (j+1) * pairCumulative D u S h (j+1) ^ 2 ≤ -(Q j) h := by
  have hunonneg (i : ℕ) : 0 ≤ u i := by
    by_cases hi : i = 0 ∨ D ≤ i
    · rw [uzero i hi]
    · push Not at hi
      exact (hu i (by omega) (by omega)).le
  have hpos : 0 < u (j-1) ∨ 0 < u (j+1) ∨ 0 < u j := by
    by_cases h0 : j = 0
    · subst j
      exact Or.inr (Or.inl (hu 1 (by omega) (by omega)))
    by_cases hjD : j = D
    · exact Or.inl (hu (j-1) (by omega) (by omega))
    · exact Or.inr (Or.inr (hu j (by omega) (by omega)))
  have ha : (pairPrevious S j) h =
      u j * pairCumulative D u S h j - u (j-1) * pairCumulative D u S h (j-1) := by
    by_cases hj0 : j = 0
    · simp [hj0, pairPrevious, pairCumulative]
    · rw [pairPrevious, ite_eq_right hj0]
      have ht := pairCumulative_difference D u S hu h hbal (j-1) (by omega)
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using ht
  have hb : S j h = u (j+1) * pairCumulative D u S h (j+1) -
      u j * pairCumulative D u S h j := by
    by_cases hjD : j = D
    · simp [hjD, sD, pairCumulative]
    · exact pairCumulative_difference D u S hu h hbal j (by omega)
  exact pair_one (Q j) (pairPrevious S j) (S j) _ _ _
    (hunonneg _) (hunonneg _) hpos hs h _ _ _ ha hb

 
theorem discrete_laplacian_sum (a : ℕ → ℝ) (D : ℕ)
    (h0 : a 0 = 0) (hD : a D = 0) (hnext : a (D+1) = 0) :
    ∑ j ∈ Finset.range (D+1), (2 * a j - a (j-1) - a (j+1)) = 0 := by
  have hp : ∑ j ∈ Finset.range (D+1), a (j-1) = ∑ j ∈ Finset.range (D+1), a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp [h0, hD]
  have hn : ∑ j ∈ Finset.range (D+1), a (j+1) = ∑ j ∈ Finset.range (D+1), a j := by
    have ht := Finset.sum_range_succ' a (D+1)
    rw [Finset.sum_range_succ, hnext, h0, add_zero, add_zero] at ht
    exact ht.symm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hp, hn]
  ring

 

theorem pair_summation_signature (D : ℕ) (hD : 2 ≤ D) (u : ℕ → ℝ)
    (S : ℕ → V →ₗ[ℝ] ℝ) (Q : ℕ → QuadraticForm ℝ V)
    (hu : ∀ j, 0 < j → j < D → 0 < u j)
    (uzero : ∀ j, j = 0 ∨ D ≤ j → u j = 0) (sD : S D = 0)
    (hs : ∀ j, j ≤ D → sigPos (pairForm (Q j) (pairPrevious S j) (S j)
      (u (j-1)) (u j) (u (j+1))) ≤ 1) :
    sigPos (∑ j ∈ Finset.range (D+1), Q j) ≤ 1 := by
  apply sigPos_le_one_of_kernel _ (∑ l ∈ Finset.range D, S l)
  intro h hbal
  have hb : ∑ l ∈ Finset.range D, S l h = 0 := by simpa using hbal
  let a := fun j => u j * pairCumulative D u S h j ^ 2
  have ht : ∑ j ∈ Finset.range (D+1), (2 * a j - a (j-1) - a (j+1)) = 0 := by
    apply discrete_laplacian_sum
    all_goals simp [a, pairCumulative]
  have hsum : ∑ j ∈ Finset.range (D+1), (2 * a j - a (j-1) - a (j+1)) ≤
      ∑ j ∈ Finset.range (D+1), -(Q j) h := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ D := by simpa using Finset.mem_range.mp hj
    simpa only [a, mul_assoc] using
      pair_sequence_one D hD u S Q hu uzero sD h hb j hj' (hs j hj')
  rw [ht, Finset.sum_neg_distrib] at hsum
  simpa using neg_nonneg.mp hsum

 

theorem discrete_summation_by_parts (a w : ℕ → ℝ) (D : ℕ)
    (h0 : a 0 = 0) (hD : a D = 0) (hnext : a (D+1) = 0) :
    (∑ j ∈ Finset.range (D+1), w j * (2 * a j - a (j-1) - a (j+1))) =
      ∑ j ∈ Finset.range (D+1), (2 * w j - w (j-1) - w (j+1)) * a j := by
  have hp : ∑ j ∈ Finset.range (D+1), w j * a (j-1) =
      ∑ j ∈ Finset.range (D+1), w (j+1) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp [h0, hD]
  have hn : ∑ j ∈ Finset.range (D+1), w j * a (j+1) =
      ∑ j ∈ Finset.range (D+1), w (j-1) * a j := by
    have ht := Finset.sum_range_succ' (fun j => w (j-1) * a j) (D+1)
    rw [Finset.sum_range_succ] at ht
    simpa [h0, hnext] using ht.symm
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hp, hn]
  have ht : ∑ j ∈ Finset.range (D+1), w j * (2 * a j) =
      ∑ j ∈ Finset.range (D+1), 2 * w j * a j := by
    apply Finset.sum_congr rfl
    intros
    ring
  rw [ht]
  ring

theorem discrete_quadratic_weight (a : ℕ → ℝ) (D : ℕ)
    (h0 : a 0 = 0) (hD : a D = 0) (hnext : a (D+1) = 0) :
    (∑ j ∈ Finset.range (D+1), (j : ℝ) * (D - j) *
      (2 * a j - a (j-1) - a (j+1))) = 2 * ∑ j ∈ Finset.range (D+1), a j := by
  rw [discrete_summation_by_parts a (fun j => (j : ℝ) * (D-j)) D h0 hD hnext,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0, h0]
  · rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one, Nat.cast_add, Nat.cast_one]
    ring

 

theorem pair_summation_weighted (D : ℕ) (hD : 2 ≤ D) (u : ℕ → ℝ)
    (S : ℕ → V →ₗ[ℝ] ℝ) (Q : ℕ → QuadraticForm ℝ V)
    (hu : ∀ j, 0 < j → j < D → 0 < u j)
    (uzero : ∀ j, j = 0 ∨ D ≤ j → u j = 0) (sD : S D = 0)
    (hs : ∀ j, 0 < j → j < D → sigPos (pairForm (Q j) (pairPrevious S j) (S j)
      (u (j-1)) (u j) (u (j+1))) ≤ 1)
    (h : V) (hbal : ∑ l ∈ Finset.range D, S l h = 0) :
    2 * (∑ j ∈ Finset.range (D+1), u j * pairCumulative D u S h j ^ 2) ≤
      -(∑ j ∈ Finset.range (D+1), ((j : ℝ) * (D-j)) • Q j) h := by
  let a := fun j => u j * pairCumulative D u S h j ^ 2
  have ha0 : a 0 = 0 := by simp [a, pairCumulative]
  have haD : a D = 0 := by simp [a, pairCumulative]
  have haN : a (D+1) = 0 := by simp [a, pairCumulative]
  have ht := discrete_quadratic_weight a D ha0 haD haN
  have hsum :
      (∑ j ∈ Finset.range (D+1), (j : ℝ) * (D-j) * (2*a j-a (j-1)-a (j+1))) ≤
      ∑ j ∈ Finset.range (D+1), -((j : ℝ) * (D-j)) * (Q j) h := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ D := by simpa using Finset.mem_range.mp hj
    by_cases hj0 : j = 0
    · simp [hj0]
    by_cases hjD : j = D
    · simp [hjD]
    have h := pair_sequence_one D hD u S Q hu uzero sD h hbal j hj'
      (hs j (by omega) (by omega))
    have hw : 0 ≤ (j : ℝ) * (D-j) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (Nat.cast_le.mpr hj'))
    simpa only [a, mul_assoc, mul_neg, neg_mul] using mul_le_mul_of_nonneg_left h hw
  rw [ht] at hsum
  simpa only [a, sum_apply, smul_apply, smul_eq_mul,
    neg_mul, Finset.sum_neg_distrib] using hsum

section Laminar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 
omit [Fintype ι] in
theorem chain_product_telescope (s : Finset (Finset ι)) (g : Finset ι → ℝ)
    (hc : ∀ G ∈ s, ∀ H ∈ s, G ⊆ H ∨ H ⊆ G) :
    ∏ G ∈ s, g G = 1 - ∑ G ∈ s, (1-g G) * ∏ H ∈ s.filter (G ⊂ ·), g H := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · simp [he]
    obtain ⟨G, hG, hmin⟩ := s.exists_min_image Finset.card (Finset.nonempty_iff_ne_empty.mpr he)
    have hsmall (H) (hH : H ∈ s.erase G) : G ⊂ H := by
      obtain ⟨hHG, hHs⟩ := Finset.mem_erase.mp hH
      rcases hc G hG H hHs with h | h
      · exact Finset.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm hHG⟩
      · have heq := Finset.eq_of_subset_of_card_le h (hmin H hHs)
        exact (hHG heq).elim
    have hfilter (H) (hH : H ∈ s.erase G) :
        s.filter (H ⊂ ·) = (s.erase G).filter (H ⊂ ·) := by
      ext J
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hJ, hHJ⟩
        refine ⟨⟨?_, hJ⟩, hHJ⟩
        intro heq
        subst J
        have hGH := Finset.ssubset_iff_subset_ne.mp (hsmall H hH)
        exact hGH.2 (Finset.Subset.antisymm hGH.1 (Finset.ssubset_iff_subset_ne.mp hHJ).1)
      · tauto
    have hGeq : s.filter (G ⊂ ·) = s.erase G := by
      ext H
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hH, hGH⟩
        exact ⟨(Finset.ssubset_iff_subset_ne.mp hGH).2.symm, hH⟩
      · intro hH
        exact ⟨hH.2, hsmall H (Finset.mem_erase.mpr hH)⟩
    have ht := ih (s.erase G) (Finset.erase_ssubset hG)
      (fun H hH J hJ => hc H (Finset.mem_of_mem_erase hH) J (Finset.mem_of_mem_erase hJ))
    have hp : ∏ H ∈ s, g H = g G * ∏ H ∈ s.erase G, g H :=
      (Finset.mul_prod_erase s g hG).symm
    have hs : ∑ H ∈ s, (1-g H) * ∏ J ∈ s.filter (H ⊂ ·), g J =
        (1-g G) * (∏ H ∈ s.erase G, g H) +
          ∑ H ∈ s.erase G, (1-g H) * ∏ J ∈ (s.erase G).filter (H ⊂ ·), g J := by
      rw [← Finset.add_sum_erase s _ hG, hGeq]
      congr 1
      apply Finset.sum_congr rfl
      intro H hH
      rw [hfilter H hH]
    rw [hp, hs]
    linarith

 
def IsLaminar (s : Finset (Finset ι)) : Prop :=
  ∀ G ∈ s, ∀ H ∈ s, G ⊆ H ∨ H ⊆ G ∨ Disjoint G H

noncomputable def laminarCoefficient (s : Finset (Finset ι))
    (g : Finset ι → ℝ) (G : Finset ι) : ℝ :=
  (1-g G) * ∏ H ∈ s.filter (G ⊂ ·), g H

 
omit [Fintype ι] in
theorem laminar_blocks (s : Finset (Finset ι)) (g : Finset ι → ℝ)
    (hl : IsLaminar s) (i j : ι) :
    (∏ G ∈ s.filter (fun G => i ∈ G ∧ j ∈ G), g G) =
      1 - ∑ G ∈ s, if i ∈ G ∧ j ∈ G then laminarCoefficient s g G else 0 := by
  classical
  let t := s.filter (fun G => i ∈ G ∧ j ∈ G)
  have hc : ∀ G ∈ t, ∀ H ∈ t, G ⊆ H ∨ H ⊆ G := by
    intro G hG H hH
    obtain ⟨hGs, hiG, _⟩ := Finset.mem_filter.mp hG
    obtain ⟨hHs, hiH, _⟩ := Finset.mem_filter.mp hH
    rcases hl G hGs H hHs with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (Finset.disjoint_left.mp h hiG hiH).elim
  have hf (G) (hG : G ∈ t) : t.filter (G ⊂ ·) = s.filter (G ⊂ ·) := by
    obtain ⟨hGs, hiG, hjG⟩ := Finset.mem_filter.mp hG
    ext H
    simp only [t, Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hH, hGH⟩
      exact ⟨⟨hH, (Finset.ssubset_iff_subset_ne.mp hGH).1 hiG,
        (Finset.ssubset_iff_subset_ne.mp hGH).1 hjG⟩, hGH⟩
  rw [show (∑ G ∈ s, if i ∈ G ∧ j ∈ G then laminarCoefficient s g G else 0) =
      ∑ G ∈ t, laminarCoefficient s g G by simp [t, Finset.sum_filter]]
  rw [chain_product_telescope t g hc]
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  rw [hf G hG]
  rfl

 

noncomputable def matrixForm (M : ι → ι → ℝ) : QuadraticForm ℝ (ι → ℝ) :=
  ∑ i, ∑ j, M i j • linMulLin (LinearMap.proj i) (LinearMap.proj j)

omit [DecidableEq ι] in
theorem matrixForm_apply (M : ι → ι → ℝ) (x : ι → ℝ) :
    matrixForm M x = ∑ i, ∑ j, M i j * x i * x j := by
  simp [matrixForm, linMulLin_apply, mul_assoc]

 
theorem laminar_quadratic (s : Finset (Finset ι)) (g : Finset ι → ℝ)
    (hl : IsLaminar s) (z : ι → ℝ) :
    (∑ i, ∑ j, (∏ G ∈ s.filter (fun G => i ∈ G ∧ j ∈ G), g G) * z i * z j) =
      (∑ i, z i)^2 - ∑ G ∈ s, laminarCoefficient s g G * (∑ i ∈ G, z i)^2 := by
  classical
  simp_rw [laminar_blocks s g hl, sub_mul, one_mul]
  simp_rw [Finset.sum_sub_distrib]
  have hfirst : (∑ i, ∑ j, z i * z j) = (∑ i, z i)^2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hfirst]
  congr 1
  simp_rw [Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  have he (i j : ι) :
      (if i ∈ G ∧ j ∈ G then laminarCoefficient s g G else 0) * z i * z j =
      laminarCoefficient s g G * (if i ∈ G then z i else 0) *
        (if j ∈ G then z j else 0) := by
    by_cases hi : i ∈ G <;> by_cases hj : j ∈ G <;> simp [hi, hj]
  simp_rw [he, ← Finset.mul_sum, ← Finset.sum_mul]
  simp [pow_two, ← Finset.mul_sum, mul_assoc]

 
omit [Fintype ι] in
theorem laminarCoefficient_nonneg (s : Finset (Finset ι))
    (g : Finset ι → ℝ) (hg : ∀ G ∈ s, 0 ≤ g G ∧ g G ≤ 1)
    (G : Finset ι) (hG : G ∈ s) : 0 ≤ laminarCoefficient s g G := by
  apply mul_nonneg (sub_nonneg.mpr (hg G hG).2)
  exact Finset.prod_nonneg fun H hH => (hg H (Finset.mem_filter.mp hH).1).1

 

theorem laminar_matrix_signature (s : Finset (Finset ι)) (g : Finset ι → ℝ)
    (hl : IsLaminar s) (hg : ∀ G ∈ s, 0 ≤ g G ∧ g G ≤ 1)
    (W : ℝ) (hW : 0 ≤ W) (α e : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    sigPos (matrixForm (fun i j =>
      W * α i * α j * (∏ G ∈ s.filter (fun G => i ∈ G ∧ j ∈ G), g G) -
        if i = j then e i else 0)) ≤ 1 := by
  classical
  apply sigPos_le_one_of_kernel _ (∑ i, α i • LinearMap.proj i)
  intro x hx
  have hx' : ∑ i, α i * x i = 0 := by simpa using hx
  rw [matrixForm_apply]
  have hexp :
      (∑ i, ∑ j, (W * α i * α j *
        (∏ G ∈ s.filter (fun G => i ∈ G ∧ j ∈ G), g G) -
        if i = j then e i else 0) * x i * x j) =
      W * ((∑ i, α i * x i)^2 -
        ∑ G ∈ s, laminarCoefficient s g G * (∑ i ∈ G, α i * x i)^2) -
        ∑ i, e i * x i^2 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    · rw [← laminar_quadratic s g hl (fun i => α i * x i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      simp [ite_mul, pow_two, mul_assoc]
  rw [hexp, hx', zero_pow (by decide : 2 ≠ 0), zero_sub]
  have ha : 0 ≤ ∑ G ∈ s, laminarCoefficient s g G * (∑ i ∈ G, α i * x i)^2 :=
    Finset.sum_nonneg fun G hG => mul_nonneg (laminarCoefficient_nonneg s g hg G hG) (sq_nonneg _)
  have hd : 0 ≤ ∑ i, e i * x i^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (he i) (sq_nonneg _)
  nlinarith

 
noncomputable def factorRemoval (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (t : Finset ι → ℤ) (i j : ι) : ℝ :=
  ∏ G ∈ s, ψ G (t G - (if i ∈ G then 1 else 0) - (if j ∈ G then 1 else 0))

noncomputable def factorRatio (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (t : Finset ι → ℤ) (i : ι) : ℝ :=
  ∏ G ∈ s.filter (i ∈ ·), ψ G (t G-1) / ψ G (t G)

noncomputable def factorGamma (ψ : Finset ι → ℤ → ℝ) (t : Finset ι → ℤ)
    (G : Finset ι) : ℝ := ψ G (t G) * ψ G (t G-2) / ψ G (t G-1)^2

 

omit [Fintype ι] in
theorem factorRemoval_eq (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (t : Finset ι → ℤ)
    (hψ : ∀ G ∈ s, ∀ z, 0 < ψ G z) (i j : ι) :
    factorRemoval s ψ t i j = (∏ G ∈ s, ψ G (t G)) *
      factorRatio s ψ t i * factorRatio s ψ t j *
      ∏ G ∈ s.filter (fun G => i ∈ G ∧ j ∈ G), factorGamma ψ t G := by
  classical
  simp only [factorRemoval, factorRatio, Finset.prod_filter]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro G hG
  have ha : ψ G (t G) ≠ 0 := (hψ G hG _).ne'
  have hb : ψ G (t G-1) ≠ 0 := (hψ G hG _).ne'
  by_cases hi : i ∈ G <;> by_cases hj : j ∈ G
  · simp only [hi, hj, and_self, ↓reduceIte, factorGamma]
    rw [show t G-1-1 = t G-2 by omega]
    field_simp
  · simp only [hi, hj, and_false, ↓reduceIte, sub_zero, mul_one, sub_zero]
    field_simp
  · simp only [hi, hj, false_and, ↓reduceIte, sub_zero, mul_one, sub_zero]
    field_simp
  · simp [hi, hj]

 

noncomputable def truncatedFactorMatrix (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (t : Finset ι → ℤ) (p : ι → ℤ) (i j : ι) : ℝ :=
  if p i = 0 ∨ p j = 0 ∨ (i = j ∧ p i = 1) then 0 else factorRemoval s ψ t i j

 

theorem truncated_laminar_signature (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (t : Finset ι → ℤ) (p : ι → ℤ)
    (hl : IsLaminar s) (hψ : ∀ G ∈ s, ∀ z, 0 < ψ G z)
    (hc : ∀ G ∈ s, ψ G (t G) * ψ G (t G-2) ≤ ψ G (t G-1)^2) :
    sigPos (matrixForm (truncatedFactorMatrix s ψ t p)) ≤ 1 := by
  classical
  let g := factorGamma ψ t
  let W := ∏ G ∈ s, ψ G (t G)
  let α := fun i => if p i = 0 then 0 else factorRatio s ψ t i
  let e := fun i => if p i = 1 then
    W * α i * α i * (∏ G ∈ s.filter (fun G => i ∈ G ∧ i ∈ G), g G) else 0
  have hg : ∀ G ∈ s, 0 ≤ g G ∧ g G ≤ 1 := by
    intro G hG
    dsimp [g, factorGamma]
    exact ⟨div_nonneg (mul_pos (hψ G hG _) (hψ G hG _)).le (sq_nonneg _),
      (div_le_one (sq_pos_of_pos (hψ G hG _))).mpr (hc G hG)⟩
  have hW : 0 ≤ W := (Finset.prod_pos fun G hG => hψ G hG _).le
  have he : ∀ i, 0 ≤ e i := by
    intro i
    dsimp [e]
    split_ifs
    · rw [mul_assoc W, ← pow_two]
      apply mul_nonneg (mul_nonneg hW (sq_nonneg _))
      exact Finset.prod_nonneg fun G hG => (hg G (Finset.mem_filter.mp hG).1).1
    · exact le_rfl
  have hM : truncatedFactorMatrix s ψ t p = fun i j =>
      W * α i * α j * (∏ G ∈ s.filter (fun G => i ∈ G ∧ j ∈ G), g G) -
        if i = j then e i else 0 := by
    funext i j
    rw [truncatedFactorMatrix]
    by_cases hi : p i = 0
    · simp [hi, α, e]
    by_cases hj : p j = 0
    · by_cases hij : i = j
      · subst j; contradiction
      · simp [hj, hij, α, e]
    by_cases hij : i = j
    · subst j
      by_cases hi1 : p i = 1
      · simp [hi1, e]
      · simp [hi, hi1, α, e, factorRemoval_eq s ψ t hψ, W, g]
    · simp [hi, hj, hij, α, factorRemoval_eq s ψ t hψ, W, g]
  rw [hM]
  exact laminar_matrix_signature s g hl hg W hW α e he

 

def removePair (p : ι → ℤ) (i j : ι) : ι → ℤ :=
  fun k => p k - (if k = i then 1 else 0) - (if k = j then 1 else 0)

def InBox (B p : ι → ℤ) : Prop := ∀ i, 0 ≤ p i ∧ p i ≤ B i

noncomputable def twoRemoval (f : (ι → ℤ) → ℝ) (p : ι → ℤ) : ι → ι → ℝ :=
  fun i j => f (removePair p i j)

 
def HasSignature (f : (ι → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ) : Prop :=
  ∀ p, InBox B p → (∑ i, p i) = T+2 → sigPos (matrixForm (twoRemoval f p)) ≤ 1

 
def PositiveSlice (f : (ι → ℤ) → ℝ) (B : ι → ℤ) (T : ℤ) : Prop :=
  (∀ p, InBox B p → (∑ i, p i) = T → 0 < f p) ∧
  (∀ p, ¬(InBox B p ∧ (∑ i, p i) = T) → f p = 0)

omit [Fintype ι] in
theorem sum_removePair (G : Finset ι) (p : ι → ℤ) (i j : ι) :
    (∑ k ∈ G, removePair p i j k) =
      (∑ k ∈ G, p k) - (if i ∈ G then 1 else 0) - (if j ∈ G then 1 else 0) := by
  simp [removePair, Finset.sum_sub_distrib]

omit [Fintype ι] in
theorem removePair_comm (p : ι → ℤ) (i j : ι) : removePair p i j = removePair p j i := by
  funext k
  simp only [removePair]
  omega

omit [Fintype ι] in
theorem removePair_inBox_iff (B p : ι → ℤ) (hp : InBox B p) (i j : ι) :
    InBox B (removePair p i j) ↔ ¬(p i = 0 ∨ p j = 0 ∨ (i = j ∧ p i = 1)) := by
  constructor
  · intro h hbad
    obtain h1 := (h i).1
    obtain h2 := (h j).1
    simp only [removePair, ↓reduceIte] at h1 h2
    rcases hbad with hi | hj | ⟨rfl, hi⟩
    · split_ifs at h1 <;> omega
    · split_ifs at h2 <;> omega
    · simp [hi] at h1
  · intro h k
    obtain ⟨hk0, hkB⟩ := hp k
    dsimp [removePair]
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst i; subst j
      simp only [not_or, not_and, true_implies] at h
      simp only [↓reduceIte]
      omega
    · subst i
      simp only [↓reduceIte, hkj, sub_zero]
      have : p k ≠ 0 := fun hh => h (Or.inl hh)
      omega
    · subst j
      simp only [hki, ↓reduceIte, sub_zero]
      have : p k ≠ 0 := fun hh => h (Or.inr (Or.inl hh))
      omega
    · simpa [hki, hkj] using hp k

noncomputable def factorSlice (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (B : ι → ℤ) (T : ℤ) (p : ι → ℤ) : ℝ := by
  classical
  exact if InBox B p ∧ (∑ i, p i) = T then ∏ G ∈ s, ψ G (∑ i ∈ G, p i) else 0

omit [DecidableEq ι] in
theorem factorSlice_positive (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (B : ι → ℤ) (T : ℤ)
    (hψ : ∀ G ∈ s, ∀ z, 0 < ψ G z) : PositiveSlice (factorSlice s ψ B T) B T := by
  constructor
  · intro p hb ht
    simp only [factorSlice, hb, ht, and_self, ↓reduceIte]
    exact Finset.prod_pos fun G hG => hψ G hG _
  · intro p h
    simp [factorSlice, h]

 

theorem factorSlice_signature (s : Finset (Finset ι))
    (ψ : Finset ι → ℤ → ℝ) (B : ι → ℤ) (T : ℤ)
    (hl : IsLaminar s) (hψ : ∀ G ∈ s, ∀ z, 0 < ψ G z)
    (hc : ∀ G ∈ s, ∀ z, ψ G z * ψ G (z-2) ≤ ψ G (z-1)^2) :
    HasSignature (factorSlice s ψ B T) B T := by
  intro p hp ht
  have hM : twoRemoval (factorSlice s ψ B T) p =
      truncatedFactorMatrix s ψ (fun G => ∑ i ∈ G, p i) p := by
    funext i j
    have htotal : (∑ k, removePair p i j k) = T := by
      rw [sum_removePair]
      simpa [ht] using (show T+2-1-1 = T by omega)
    simp only [twoRemoval, factorSlice, truncatedFactorMatrix, htotal, and_true,
      removePair_inBox_iff B p hp i j]
    split_ifs <;> simp_all [factorRemoval, sum_removePair]
  rw [hM]
  exact truncated_laminar_signature s ψ _ p hl hψ (fun G hG => hc G hG _)

end Laminar

section ScalarFactors

 
def PosLogConcave (ψ : ℤ → ℝ) : Prop :=
  (∀ z, 0 < ψ z) ∧ (∀ z, ψ z * ψ (z-2) ≤ ψ (z-1)^2)

theorem posLogConcave_of_convex_exponent (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (D : ℤ → ℕ) (hD : ∀ z, 2 * D (z-1) ≤ D z + D (z-2)) :
    PosLogConcave (fun z => η ^ D z) := by
  refine ⟨fun z => pow_pos hη _, ?_⟩
  intro z
  rw [← pow_add, ← pow_mul]
  apply pow_le_pow_of_le_one hη.le hη1.le
  simpa [Nat.mul_comm] using hD z

theorem posLogConcave_abs (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    PosLogConcave (fun z : ℤ => η ^ z.natAbs) := by
  apply posLogConcave_of_convex_exponent η hη hη1
  intro z
  have ht := Int.natAbs_add_le z (z-2)
  rw [show z+(z-2) = 2*(z-1) by ring, Int.natAbs_mul] at ht
  simpa using ht

theorem posLogConcave_positive_part (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    PosLogConcave (fun z : ℤ => η ^ z.toNat) := by
  apply posLogConcave_of_convex_exponent η hη hη1
  intro z
  omega

theorem PosLogConcave.translate {ψ : ℤ → ℝ} (h : PosLogConcave ψ) (a : ℤ) :
    PosLogConcave (fun z => ψ (z+a)) := by
  refine ⟨fun z => h.1 _, ?_⟩
  intro z
  have ht := h.2 (z+a)
  convert ht using 1 <;> congr 2 <;> ring_nf

theorem PosLogConcave.reflect {ψ : ℤ → ℝ} (h : PosLogConcave ψ) :
    PosLogConcave (fun z => ψ (-z)) := by
  refine ⟨fun z => h.1 _, ?_⟩
  intro z
  have ht := h.2 (2-z)
  rw [show 2-z-2 = -z by ring, show 2-z-1 = -(z-1) by ring] at ht
  rw [show 2-z = -(z-2) by ring, mul_comm] at ht
  exact ht

theorem posLogConcave_prod {α : Type*} (s : Finset α) (ψ : α → ℤ → ℝ)
    (hψ : ∀ a ∈ s, PosLogConcave (ψ a)) :
    PosLogConcave (fun z => ∏ a ∈ s, ψ a z) := by
  refine ⟨fun z => Finset.prod_pos fun a ha => (hψ a ha).1 z, ?_⟩
  intro z
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  exact Finset.prod_le_prod₀
    (fun a ha => mul_nonneg ((hψ a ha).1 _).le ((hψ a ha).1 _).le)
    (fun a ha => (hψ a ha).2 z)

end ScalarFactors

section IndexedFactors
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

noncomputable def groupedSequence (G : α → Finset ι) (ψ : α → ℤ → ℝ)
    (H : Finset ι) (z : ℤ) : ℝ := ∏ a ∈ Finset.univ.filter (fun a => G a = H), ψ a z

noncomputable def indexedFactorSlice (G : α → Finset ι) (ψ : α → ℤ → ℝ)
    (B : ι → ℤ) (T : ℤ) (p : ι → ℤ) : ℝ := by
  classical
  exact if InBox B p ∧ (∑ i, p i) = T then ∏ a, ψ a (∑ i ∈ G a, p i) else 0

 

omit [DecidableEq α] in
theorem indexedFactorSlice_eq (G : α → Finset ι) (ψ : α → ℤ → ℝ)
    (B : ι → ℤ) (T : ℤ) : indexedFactorSlice G ψ B T =
      factorSlice (Finset.univ.image G) (groupedSequence G ψ) B T := by
  classical
  funext p
  dsimp [indexedFactorSlice, factorSlice]
  split_ifs
  · symm
    calc
      (∏ H ∈ Finset.univ.image G, groupedSequence G ψ H (∑ i ∈ H, p i)) =
          ∏ H ∈ Finset.univ.image G, ∏ a ∈ Finset.univ.filter (fun a => G a = H),
            ψ a (∑ i ∈ G a, p i) := by
        apply Finset.prod_congr rfl
        intro H hH
        apply Finset.prod_congr rfl
        intro a ha
        rw [(Finset.mem_filter.mp ha).2]
      _ = ∏ a, ψ a (∑ i ∈ G a, p i) :=
        Finset.prod_fiberwise_of_maps_to (fun a _ => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩) _
  · rfl

omit [DecidableEq α] in
theorem indexedFactorSlice_signature (G : α → Finset ι) (ψ : α → ℤ → ℝ)
    (B : ι → ℤ) (T : ℤ)
    (hl : ∀ a b, G a ⊆ G b ∨ G b ⊆ G a ∨ Disjoint (G a) (G b))
    (hψ : ∀ a, PosLogConcave (ψ a)) : HasSignature (indexedFactorSlice G ψ B T) B T := by
  rw [indexedFactorSlice_eq]
  have hp (H : Finset ι) : PosLogConcave (groupedSequence G ψ H) :=
    posLogConcave_prod _ ψ (fun a _ => hψ a)
  apply factorSlice_signature
  · rintro H hH J hJ
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hJ
    exact hl a b
  · exact fun H _ => (hp H).1
  · exact fun H _ => (hp H).2

end IndexedFactors

section SoftWeight
variable {m n : ℕ}

abbrev Cell (m n : ℕ) := Fin m × Fin n
abbrev Coordinate (m n : ℕ) := Bool × Cell m n
abbrev FactorLabel (m n : ℕ) := (Fin m ⊕ Fin n) × Bool

 

def coordinateLine (a : Coordinate m n) : Fin m ⊕ Fin n :=
  if a.1 then Sum.inl a.2.1 else Sum.inr a.2.2

def softFactorSet (small : Finset (Cell m n)) (a : FactorLabel m n) :
    Finset (Coordinate m n) :=
  Finset.univ.filter fun v => coordinateLine v = a.1 ∧ (a.2 = true → v.2 ∈ small)

theorem softFactorSet_laminar (small : Finset (Cell m n)) :
    ∀ a b, softFactorSet small a ⊆ softFactorSet small b ∨
      softFactorSet small b ⊆ softFactorSet small a ∨
      Disjoint (softFactorSet small a) (softFactorSet small b) := by
  rintro ⟨l, a⟩ ⟨k, b⟩
  by_cases h : l = k
  · subst k
    cases a <;> cases b
    · exact Or.inl (Finset.Subset.refl _)
    · right; left
      intro v hv
      simp only [softFactorSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.false_eq_true, false_implies, and_true] at *
      exact hv.1
    · left
      intro v hv
      simp only [softFactorSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Bool.false_eq_true, false_implies, and_true] at *
      exact hv.1
    · exact Or.inl (Finset.Subset.refl _)
  · right; right
    apply Finset.disjoint_left.mpr
    intro v hv hk
    have hv' := (Finset.mem_filter.mp hv).2.1
    have hk' := (Finset.mem_filter.mp hk).2.1
    exact h (hv'.symm.trans hk')

 

def softFactorExponent (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n))
    (a : FactorLabel m n) (z : ℤ) : ℕ :=
  match a with
  | (Sum.inl i, false) => (z - rb i).natAbs
  | (Sum.inl i, true) => (z - r i).toNat
  | (Sum.inr j, false) => ((∑ i, B (i,j)) - z - cb j).natAbs
  | (Sum.inr j, true) => ((∑ i, if (i,j) ∈ small then B (i,j) else 0) - z - c j).toNat

noncomputable def softFactor (η : ℝ) (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) (a : FactorLabel m n) : ℤ → ℝ :=
  fun z => η ^ softFactorExponent r rb c cb B small a z

theorem softFactor_logconcave (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (r rb : Fin m → ℤ) (c cb : Fin n → ℤ) (B : Cell m n → ℤ)
    (small : Finset (Cell m n)) (a : FactorLabel m n) :
    PosLogConcave (softFactor η r rb c cb B small a) := by
  obtain ⟨l, b⟩ := a
  cases l with
  | inl i =>
    cases b
    · change PosLogConcave (fun z => η ^ (z - rb i).natAbs)
      simpa only [sub_eq_add_neg] using
        (posLogConcave_abs η hη hη1).translate (-rb i)
    · change PosLogConcave (fun z => η ^ (z - r i).toNat)
      simpa only [sub_eq_add_neg] using
        (posLogConcave_positive_part η hη hη1).translate (-r i)
  | inr j =>
    cases b
    · have h := ((posLogConcave_abs η hη hη1).translate
        ((∑ i, B (i,j)) - cb j)).reflect
      convert h using 1
      funext z
      dsimp [softFactor, softFactorExponent]
      congr 2
      ring
    · have h := ((posLogConcave_positive_part η hη hη1).translate
        ((∑ i, if (i,j) ∈ small then B (i,j) else 0) - c j)).reflect
      convert h using 1
      funext z
      dsimp [softFactor, softFactorExponent]
      congr 2
      ring

 

def softPenalty (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) (p : Coordinate m n → ℤ) : ℕ :=
  ∑ a : FactorLabel m n, softFactorExponent r rb c cb B small a
    (∑ v ∈ softFactorSet small a, p v)

noncomputable def softWeight (η : ℝ) (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) (p : Coordinate m n → ℤ) : ℝ := by
  classical
  exact if InBox (fun v => B v.2) p ∧ (∑ v, p v) = ∑ s, B s
    then η ^ softPenalty r rb c cb B small p else 0

theorem softWeight_eq_factorSlice (η : ℝ) (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) :
    softWeight η r rb c cb B small = indexedFactorSlice (softFactorSet small)
      (softFactor η r rb c cb B small) (fun v => B v.2) (∑ s, B s) := by
  classical
  funext p
  simp only [softWeight, indexedFactorSlice]
  split_ifs
  · simp [softPenalty, softFactor, Finset.prod_pow_eq_pow_sum]
  · rfl

theorem softWeight_signature (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (r rb : Fin m → ℤ) (c cb : Fin n → ℤ) (B : Cell m n → ℤ)
    (small : Finset (Cell m n)) :
    HasSignature (softWeight η r rb c cb B small) (fun v => B v.2) (∑ s, B s) := by
  rw [softWeight_eq_factorSlice]
  apply indexedFactorSlice_signature
  · exact softFactorSet_laminar small
  · exact softFactor_logconcave η hη hη1 r rb c cb B small

theorem softFactorSet_sum_row (small : Finset (Cell m n)) (p : Coordinate m n → ℤ)
    (i : Fin m) (b : Bool) :
    (∑ v ∈ softFactorSet small (Sum.inl i,b), p v) =
      ∑ j, if b = true → (i,j) ∈ small then p (true,(i,j)) else 0 := by
  cases b <;>
    simp [softFactorSet, coordinateLine, Finset.sum_filter, Fintype.sum_prod_type,
      ite_and, Finset.sum_ite_irrel]

theorem softFactorSet_sum_col (small : Finset (Cell m n)) (p : Coordinate m n → ℤ)
    (j : Fin n) (b : Bool) :
    (∑ v ∈ softFactorSet small (Sum.inr j,b), p v) =
      ∑ i, if b = true → (i,j) ∈ small then p (false,(i,j)) else 0 := by
  cases b <;>
    simp [softFactorSet, coordinateLine, Finset.sum_filter, Fintype.sum_prod_type,
      ite_and]

 

theorem softPenalty_expansion (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) (p : Coordinate m n → ℤ) :
    softPenalty r rb c cb B small p =
      (∑ i, ((∑ j, p (true,(i,j))) - rb i).natAbs) +
      (∑ j, ((∑ i, (B (i,j) - p (false,(i,j)))) - cb j).natAbs) +
      (∑ i, ((∑ j, if (i,j) ∈ small then p (true,(i,j)) else 0) - r i).toNat) +
      (∑ j, ((∑ i, if (i,j) ∈ small then B (i,j) - p (false,(i,j)) else 0) - c j).toNat) := by
  simp only [softPenalty, Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [softFactorSet_sum_row, softFactorSet_sum_col, Bool.false_eq_true,
    false_implies, ite_true, true_implies, softFactorExponent]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsplit (j : Fin n) :
      (∑ i, if (i,j) ∈ small then B (i,j) - p (false,(i,j)) else 0) =
      (∑ i, if (i,j) ∈ small then B (i,j) else 0) -
      (∑ i, if (i,j) ∈ small then p (false,(i,j)) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hcol (j : Fin n) :
      (∑ i, (B (i,j) - p (false,(i,j)))) = (∑ i, B (i,j)) - (∑ i, p (false,(i,j))) :=
    Finset.sum_sub_distrib (s := Finset.univ) (fun i : Fin m => B (i,j))
      (fun i => p (false,(i,j)))
  simp only [hsplit]
  omega

end SoftWeight

section BalancedClosure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 
def pairAssembly {R : Type*} (p : ι → R) (a b : R) : ι ⊕ Bool → R :=
  Sum.elim p (fun t => if t then a else b)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pairAssembly_old {R : Type*} (p : ι → R) (a b : R) (i : ι) :
    pairAssembly p a b (Sum.inl i) = p i := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pairAssembly_first {R : Type*} (p : ι → R) (a b : R) :
    pairAssembly p a b (Sum.inr true) = a := rfl
omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pairAssembly_second {R : Type*} (p : ι → R) (a b : R) :
    pairAssembly p a b (Sum.inr false) = b := rfl

noncomputable def pairAssemblyLinear : ((ι → ℝ) × ℝ × ℝ) →ₗ[ℝ] (ι ⊕ Bool → ℝ) where
  toFun v := pairAssembly v.1 v.2.1 v.2.2
  map_add' := by intros; funext i; cases i with
    | inl i => rfl
    | inr b => cases b <;> rfl
  map_smul' := by intros; funext i; cases i with
    | inl i => rfl
    | inr b => cases b <;> rfl

 

theorem signature_comp {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (Q : QuadraticForm ℝ V) (hs : sigPos Q ≤ 1)
    (L : W →ₗ[ℝ] V) : sigPos (Q.comp L) ≤ 1 := by
  by_cases h : ∃ e, 0 < Q e
  · obtain ⟨e, he⟩ := h
    apply sigPos_le_one_of_kernel _ ((Q.associated e).comp L)
    intro x hx
    have hp := positive_projection Q hs e (L x) he
    have hc : Q.associated (L x) e = 0 := by
      rw [QuadraticMap.associated_isSymm ℝ Q]
      exact hx
    simpa [hc] using hp
  · push Not at h
    apply sigPos_le_one_of_kernel _ 0
    intro x _
    exact h (L x)

noncomputable def columnLinear (s : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, (s i) • LinearMap.proj i

omit [DecidableEq ι] in
@[simp] theorem columnLinear_apply (s h : ι → ℝ) :
    columnLinear s h = ∑ i, s i * h i := by simp [columnLinear]

 
omit [DecidableEq ι] in
theorem matrixForm_pairAssembly (M : (ι ⊕ Bool) → (ι ⊕ Bool) → ℝ)
    (hsym : ∀ i j, M i j = M j i) :
    (matrixForm M).comp pairAssemblyLinear =
      pairForm (matrixForm (fun i j => M (Sum.inl i) (Sum.inl j)))
        (columnLinear fun i => M (Sum.inl i) (Sum.inr true))
        (columnLinear fun i => M (Sum.inl i) (Sum.inr false))
        (M (Sum.inr true) (Sum.inr true)) (M (Sum.inr true) (Sum.inr false))
        (M (Sum.inr false) (Sum.inr false)) := by
  ext v
  obtain ⟨h,a,b⟩ := v
  simp only [QuadraticMap.comp_apply, pairAssemblyLinear, LinearMap.coe_mk, AddHom.coe_mk,
    matrixForm_apply, Fintype.sum_sum_type, Fintype.sum_bool, pairAssembly_old,
    pairAssembly_first, pairAssembly_second, pairForm_apply, columnLinear_apply]
  simp_rw [hsym (Sum.inr true) (Sum.inl _), hsym (Sum.inr false) (Sum.inl _),
    hsym (Sum.inr false) (Sum.inr true)]
  have h1 : (∑ i, M (Sum.inl i) (Sum.inr true) * a * h i) =
      (∑ i, M (Sum.inl i) (Sum.inr true) * h i) * a := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, M (Sum.inl i) (Sum.inr false) * b * h i) =
      (∑ i, M (Sum.inl i) (Sum.inr false) * h i) * b := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, h2]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

def removeOne (p : ι → ℤ) (i : ι) : ι → ℤ :=
  fun k => p k - if k = i then 1 else 0

omit [DecidableEq ι] in
theorem pairAssembly_sum (p : ι → ℤ) (a b : ℤ) :
    (∑ i, pairAssembly p a b i) = (∑ i, p i) + a + b := by
  simp [Fintype.sum_sum_type, pairAssembly, add_assoc]

omit [Fintype ι] [DecidableEq ι] in
theorem pairAssembly_inBox (B p : ι → ℤ) (C a b : ℤ) :
    InBox (pairAssembly B C C) (pairAssembly p a b) ↔
      InBox B p ∧ (0 ≤ a ∧ a ≤ C) ∧ (0 ≤ b ∧ b ≤ C) := by
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inl i), h (Sum.inr true), h (Sum.inr false)⟩
  · rintro ⟨hp, ha, hb⟩ i
    cases i with
    | inl i => exact hp i
    | inr b => cases b
               · exact hb
               · exact ha

theorem PositiveSlice.zero_of_negative {κ : Type*} [Fintype κ]
    {f : (κ → ℤ) → ℝ} {B : κ → ℤ} {T : ℤ}
    (hf : PositiveSlice f B T) (p : κ → ℤ) (i : κ) (hi : p i < 0) : f p = 0 := by
  apply hf.2
  rintro ⟨h, _⟩
  exact (not_lt_of_ge (h i).1) hi

omit [Fintype ι] in
theorem removePair_pair_old (p : ι → ℤ) (a b : ℤ) (i j : ι) :
    removePair (pairAssembly p a b) (Sum.inl i) (Sum.inl j) =
      pairAssembly (removePair p i j) a b := by
  funext k
  cases k with
  | inl k => simp [removePair, pairAssembly]
  | inr k => cases k <;> simp [removePair, pairAssembly]

omit [Fintype ι] in
theorem removePair_pair_first (p : ι → ℤ) (a b : ℤ) (i : ι) :
    removePair (pairAssembly p a b) (Sum.inl i) (Sum.inr true) =
      pairAssembly (removeOne p i) (a-1) b := by
  funext k
  cases k with
  | inl k => simp [removePair, pairAssembly, removeOne]
  | inr k => cases k <;> simp [removePair, pairAssembly]

omit [Fintype ι] in
theorem removePair_pair_second (p : ι → ℤ) (a b : ℤ) (i : ι) :
    removePair (pairAssembly p a b) (Sum.inl i) (Sum.inr false) =
      pairAssembly (removeOne p i) a (b-1) := by
  funext k
  cases k with
  | inl k => simp [removePair, pairAssembly, removeOne]
  | inr k => cases k <;> simp [removePair, pairAssembly]

omit [Fintype ι] in
theorem removePair_pair_fresh (p : ι → ℤ) (a b : ℤ) (s t : Bool) :
    removePair (pairAssembly p a b) (Sum.inr s) (Sum.inr t) =
      pairAssembly p (a - (if s then 1 else 0) - (if t then 1 else 0))
        (b - (if s then 0 else 1) - (if t then 0 else 1)) := by
  funext k
  cases k with
  | inl k => simp [removePair, pairAssembly]
  | inr k => cases k <;> cases s <;> cases t <;> simp [removePair, pairAssembly]

noncomputable def pairQ (f : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (D j : ℕ) :
    QuadraticForm ℝ (ι → ℝ) :=
  matrixForm (twoRemoval (fun q => f (pairAssembly q (j:ℤ) ((D:ℤ)-j))) p)

noncomputable def pairS (f : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (D j : ℕ) :
    (ι → ℝ) →ₗ[ℝ] ℝ :=
  columnLinear (fun i => f (pairAssembly (removeOne p i) (j:ℤ) ((D:ℤ)-1-j)))

noncomputable def pairU (f : (ι ⊕ Bool → ℤ) → ℝ) (p : ι → ℤ) (D j : ℕ) : ℝ :=
  f (pairAssembly p ((j:ℤ)-1) ((D:ℤ)-1-j))

 

theorem pair_block_identity (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C T : ℤ)
    (hf : PositiveSlice f (pairAssembly B C C) T) (p : ι → ℤ) (D j : ℕ) :
    (matrixForm (twoRemoval f (pairAssembly p (j:ℤ) ((D:ℤ)-j)))).comp pairAssemblyLinear =
      pairForm (pairQ f p D j) (pairPrevious (pairS f p D) j) (pairS f p D j)
        (pairU f p D (j-1)) (pairU f p D j) (pairU f p D (j+1)) := by
  rw [matrixForm_pairAssembly (twoRemoval f (pairAssembly p (j:ℤ) ((D:ℤ)-j)))
    (fun i k => congrArg f (removePair_comm _ i k))]
  simp only [twoRemoval, removePair_pair_old, removePair_pair_first,
    removePair_pair_second, removePair_pair_fresh, ↓reduceIte, sub_zero]
  have hSa : (columnLinear fun i => f (pairAssembly (removeOne p i) ((j:ℤ)-1) ((D:ℤ)-j))) =
      pairPrevious (pairS f p D) j := by
    by_cases hj : j = 0
    · subst j
      apply LinearMap.ext
      intro h
      simp only [pairPrevious, ↓reduceIte, LinearMap.zero_apply, columnLinear_apply]
      apply Finset.sum_eq_zero
      intro i _
      have hz := hf.zero_of_negative (pairAssembly (removeOne p i) ((0:ℤ)-1) ((D:ℤ)-0))
        (Sum.inr true) (by simp)
      calc
        _ = 0 * h i := congrArg (fun z => z * h i) hz
        _ = 0 := zero_mul _
    · simp only [pairPrevious, ite_eq_right hj, pairS]
      congr 1
      funext i
      congr 2
      · simp [Nat.cast_sub (by omega : 1 ≤ j)]
      · simp [Nat.cast_sub (by omega : 1 ≤ j)]
  have haa : f (pairAssembly p ((j:ℤ)-1-1) ((D:ℤ)-j)) = pairU f p D (j-1) := by
    by_cases hj : j = 0
    · subst j
      dsimp [pairU]
      rw [hf.zero_of_negative _ (Sum.inr true) (by simp),
        hf.zero_of_negative _ (Sum.inr true) (by simp)]
    · simp only [pairU, Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
      congr 2
      ring
  rw [hSa, haa]
  congr 1
  · dsimp [pairS]
    congr 1
    funext i
    congr 2
    ring
  · dsimp [pairU]
    congr 2 <;> ring
  · dsimp [pairU]
    congr 2 <;> ring

omit [DecidableEq ι] in
theorem pairU_positive (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C : ℕ) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T) (p : ι → ℤ)
    (hp : InBox B p) (D : ℕ) (hDC : D ≤ C+1)
    (ht : (∑ i, p i) + (D:ℤ) = T+2) (j : ℕ) (hj : 0 < j) (hjD : j < D) :
    0 < pairU f p D j := by
  apply hf.1
  · rw [pairAssembly_inBox]
    exact ⟨hp, by omega, by omega⟩
  · rw [pairAssembly_sum]
    omega

omit [DecidableEq ι] in
theorem pairU_zero (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C T : ℤ)
    (hf : PositiveSlice f (pairAssembly B C C) T) (p : ι → ℤ) (D j : ℕ)
    (hj : j = 0 ∨ D ≤ j) : pairU f p D j = 0 := by
  rcases hj with rfl | hj
  · exact hf.zero_of_negative _ (Sum.inr true) (by simp [pairAssembly])
  · exact hf.zero_of_negative _ (Sum.inr false) (by dsimp [pairAssembly]; omega)

theorem pairS_top (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C T : ℤ)
    (hf : PositiveSlice f (pairAssembly B C C) T) (p : ι → ℤ) (D : ℕ) :
    pairS f p D D = 0 := by
  apply LinearMap.ext
  intro h
  simp only [pairS, columnLinear_apply, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [hf.zero_of_negative _ (Sum.inr false) (by dsimp [pairAssembly]; omega), zero_mul]

theorem pair_block_signature (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ) (C : ℕ) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (hs : HasSignature f (pairAssembly B (C:ℤ) C) T)
    (p : ι → ℤ) (hp : InBox B p) (D : ℕ)
    (ht : (∑ i, p i) + (D:ℤ) = T+2)
    (j : ℕ) (hj : j ≤ D) (hjC : j ≤ C) (hDj : D ≤ C+j) :
    sigPos (pairForm (pairQ f p D j) (pairPrevious (pairS f p D) j) (pairS f p D j)
      (pairU f p D (j-1)) (pairU f p D j) (pairU f p D (j+1))) ≤ 1 := by
  rw [← pair_block_identity f B (C:ℤ) T hf p D j]
  apply signature_comp
  apply hs
  · rw [pairAssembly_inBox]
    exact ⟨hp, by omega, by omega⟩
  · rw [pairAssembly_sum]
    omega

noncomputable def balancedMarginal (f : (ι ⊕ Bool → ℤ) → ℝ) (C : ℕ)
    (p : ι → ℤ) : ℝ := ∑ j ∈ Finset.range (C+1),
      f (pairAssembly p (j:ℤ) ((C:ℤ)-j))

omit [DecidableEq ι] in
theorem matrixForm_sum {α : Type*} (s : Finset α) (M : α → ι → ι → ℝ) :
    matrixForm (fun i k => ∑ a ∈ s, M a i k) = ∑ a ∈ s, matrixForm (M a) := by
  ext h
  simp only [matrixForm_apply, sum_apply, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ a ∈ s, ∑ k, M a i k * h i * h k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem balancedMarginal_signature (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (hC : 2 ≤ C) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (hs : HasSignature f (pairAssembly B (C:ℤ) C) T) :
    HasSignature (balancedMarginal f C) B (T-C) := by
  intro p hp ht
  have htotal : (∑ i, p i) + (C:ℤ) = T+2 := by omega
  have heq : matrixForm (twoRemoval (balancedMarginal f C) p) =
      ∑ j ∈ Finset.range (C+1), pairQ f p C j := by
    exact matrixForm_sum (Finset.range (C+1))
      (fun j i k => f (pairAssembly (removePair p i k) (j:ℤ) ((C:ℤ)-j)))
  rw [heq]
  apply pair_summation_signature C hC (pairU f p C) (pairS f p C) (pairQ f p C)
  · exact pairU_positive f B C T hf p hp C (by omega) htotal
  · exact pairU_zero f B (C:ℤ) T hf p C
  · exact pairS_top f B (C:ℤ) T hf p C
  · intro j hj
    exact pair_block_signature f B C T hf hs p hp C htotal j hj hj (by omega)

omit [DecidableEq ι] in
theorem balancedMarginal_positive (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (T : ℤ) (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T) :
    PositiveSlice (balancedMarginal f C) B (T-C) := by
  constructor
  · intro p hp ht
    apply Finset.sum_pos
    · intro j hj
      have hjC : j ≤ C := by simpa using Finset.mem_range.mp hj
      apply hf.1
      · rw [pairAssembly_inBox]
        exact ⟨hp, by omega, by omega⟩
      · rw [pairAssembly_sum]
        omega
    · exact ⟨0, by simp⟩
  · intro p hp
    apply Finset.sum_eq_zero
    intro j _
    apply hf.2
    rintro ⟨hb, ht⟩
    apply hp
    rw [pairAssembly_inBox] at hb
    rw [pairAssembly_sum] at ht
    exact ⟨hb.1, by omega⟩

 

theorem actual_pair_weighted (f : (ι ⊕ Bool → ℤ) → ℝ) (B : ι → ℤ)
    (C : ℕ) (hC : 2 ≤ C) (T : ℤ)
    (hf : PositiveSlice f (pairAssembly B (C:ℤ) C) T)
    (hs : HasSignature f (pairAssembly B (C:ℤ) C) T)
    (p : ι → ℤ) (hp : InBox B p) (ht : (∑ i, p i) + (C+1:ℕ) = T+2)
    (h : ι → ℝ) (hbal : ∑ j ∈ Finset.range (C+1), pairS f p (C+1) j h = 0) :
    2 * (∑ j ∈ Finset.range (C+2), pairU f p (C+1) j *
      pairCumulative (C+1) (pairU f p (C+1)) (pairS f p (C+1)) h j ^ 2) ≤
    -(∑ j ∈ Finset.range (C+2), ((j:ℝ) * (C+1-j)) • pairQ f p (C+1) j) h := by
  have hw := pair_summation_weighted (C+1) (by omega)
    (pairU f p (C+1)) (pairS f p (C+1)) (pairQ f p (C+1))
    (pairU_positive f B C T hf p hp (C+1) (by omega) ht)
    (pairU_zero f B (C:ℤ) T hf p (C+1))
    (pairS_top f B (C:ℤ) T hf p (C+1))
    (fun j hj hjC => pair_block_signature f B C T hf hs p hp (C+1) ht j
      (by omega) (by omega) (by omega)) h hbal
  simpa only [Nat.cast_add, Nat.cast_one] using hw

end BalancedClosure

section ReindexAndContext
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def coordinatePullback (e : ι ≃ κ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun p := p ∘ e
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [Fintype ι] [Fintype κ] in
theorem removePair_reindex (e : ι ≃ κ) (p : κ → ℤ) (i j : ι) :
    removePair (p ∘ e) i j = (removePair p (e i) (e j)) ∘ e := by
  funext k
  simp [removePair, e.injective.eq_iff]

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixForm_reindex (e : ι ≃ κ) (M : κ → κ → ℝ) :
    (matrixForm fun i j => M (e i) (e j)) = (matrixForm M).comp (coordinatePullback e.symm) := by
  ext h
  simp only [matrixForm_apply, QuadraticMap.comp_apply, coordinatePullback,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp e]
  simp

 

theorem HasSignature.reindex {f : (ι → ℤ) → ℝ} {B : ι → ℤ} {T : ℤ}
    (hf : HasSignature f B T) (e : ι ≃ κ) :
    HasSignature (fun p => f (p ∘ e)) (B ∘ e.symm) T := by
  intro p hp ht
  have hb : InBox B (p ∘ e) := by
    intro i
    simpa [Function.comp_def] using hp (e i)
  have htotal : (∑ i, (p ∘ e) i) = T+2 := by simpa [Function.comp_def, Equiv.sum_comp e] using ht
  have hs := hf (p ∘ e) hb htotal
  have hM : twoRemoval (fun p => f (p ∘ e)) p =
      fun i j => twoRemoval f (p ∘ e) (e.symm i) (e.symm j) := by
    funext i j
    simp [twoRemoval, removePair_reindex]
  rw [hM, matrixForm_reindex e.symm]
  exact signature_comp _ hs _

omit [DecidableEq ι] [DecidableEq κ] in
theorem PositiveSlice.reindex {f : (ι → ℤ) → ℝ} {B : ι → ℤ} {T : ℤ}
    (hf : PositiveSlice f B T) (e : ι ≃ κ) :
    PositiveSlice (fun p => f (p ∘ e)) (B ∘ e.symm) T := by
  have hbox (p : κ → ℤ) : InBox (B ∘ e.symm) p ↔ InBox B (p ∘ e) := by
    constructor
    · intro hp i
      simpa [Function.comp_def] using hp (e i)
    · intro hp i
      simpa [Function.comp_def] using hp (e.symm i)
  have hsum (p : κ → ℤ) : (∑ i, (p ∘ e) i) = ∑ i, p i := Equiv.sum_comp e p
  constructor
  · intro p hp ht
    apply hf.1 _ ((hbox p).mp hp)
    rw [hsum, ht]
  · intro p hp
    apply hf.2
    simpa only [← hbox, hsum] using hp

noncomputable def rightCoordinates : (κ → ℝ) →ₗ[ℝ] (ι ⊕ κ → ℝ) where
  toFun p := Sum.elim 0 p
  map_add' := by intros; funext i; cases i <;> simp
  map_smul' := by intros; funext i; cases i <;> simp

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixForm_right (M : (ι ⊕ κ) → (ι ⊕ κ) → ℝ) :
    matrixForm (fun i j => M (Sum.inr i) (Sum.inr j)) =
      (matrixForm M).comp rightCoordinates := by
  ext h
  simp [matrixForm_apply, rightCoordinates, Fintype.sum_sum_type]

omit [Fintype ι] [Fintype κ] in
theorem removePair_fixed (σ : ι → ℤ) (p : κ → ℤ) (i j : κ) :
    removePair (Sum.elim σ p) (Sum.inr i) (Sum.inr j) = Sum.elim σ (removePair p i j) := by
  funext k
  cases k <;> simp [removePair]

theorem HasSignature.fixedContext {f : (ι ⊕ κ → ℤ) → ℝ} {A : ι → ℤ} {B : κ → ℤ} {T : ℤ}
    (hf : HasSignature f (Sum.elim A B) T) (σ : ι → ℤ) (hσ : InBox A σ) :
    HasSignature (fun p => f (Sum.elim σ p)) B (T - ∑ i, σ i) := by
  intro p hp ht
  have hb : InBox (Sum.elim A B) (Sum.elim σ p) := by
    intro i
    cases i with
    | inl i => exact hσ i
    | inr i => exact hp i
  have htotal : (∑ i, Sum.elim σ p i) = T+2 := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    omega
  have hs := hf (Sum.elim σ p) hb htotal
  have hM : twoRemoval (fun p => f (Sum.elim σ p)) p =
      fun i j => twoRemoval f (Sum.elim σ p) (Sum.inr i) (Sum.inr j) := by
    funext i j
    simp [twoRemoval, removePair_fixed]
  rw [hM, matrixForm_right]
  exact signature_comp _ hs _

omit [DecidableEq ι] [DecidableEq κ] in
theorem PositiveSlice.fixedContext {f : (ι ⊕ κ → ℤ) → ℝ} {A : ι → ℤ} {B : κ → ℤ} {T : ℤ}
    (hf : PositiveSlice f (Sum.elim A B) T) (σ : ι → ℤ) (hσ : InBox A σ) :
    PositiveSlice (fun p => f (Sum.elim σ p)) B (T - ∑ i, σ i) := by
  constructor
  · intro p hp ht
    apply hf.1
    · intro i
      cases i with
      | inl i => exact hσ i
      | inr i => exact hp i
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      omega
  · intro p hp
    apply hf.2
    rintro ⟨hb, ht⟩
    apply hp
    refine ⟨fun i => hb (Sum.inr i), ?_⟩
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] at ht
    omega

end ReindexAndContext

section ManyBalanced
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def balanceBox {k : ℕ} (A : ι → ℤ) (C : Fin k → ℕ) :
    ι ⊕ (Fin k × Bool) → ℤ := Sum.elim A (fun sb => (C sb.1 : ℤ))

def balanceProfile {k : ℕ} (C : Fin k → ℕ) (a : ∀ s, Fin (C s+1)) :
    Fin k × Bool → ℤ := fun sb => if sb.2 then (a sb.1:ℕ) else (C sb.1:ℤ) - (a sb.1:ℕ)

noncomputable def balancedSlots {k : ℕ} (f : (ι ⊕ (Fin k × Bool) → ℤ) → ℝ)
    (C : Fin k → ℕ) (p : ι → ℤ) : ℝ :=
  ∑ a : ∀ s, Fin (C s+1), f (Sum.elim p (balanceProfile C a))

def splitSlot (k : ℕ) : (ι ⊕ (Fin (k+1) × Bool)) ≃ ((ι ⊕ (Fin k × Bool)) ⊕ Bool) where
  toFun := Sum.elim (fun i => Sum.inl (Sum.inl i))
    (fun sb => Fin.cases (Sum.inr sb.2) (fun s => Sum.inl (Sum.inr (s,sb.2))) sb.1)
  invFun := Sum.elim (Sum.elim Sum.inl (fun sb => Sum.inr (sb.1.succ, sb.2)))
    (fun b => Sum.inr (0,b))
  left_inv := by
    intro i
    rcases i with i | ⟨s,b⟩
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) s <;> rfl
  right_inv := by
    intro i
    rcases i with (i | ⟨s,b⟩) | b <;> rfl

def piHeadEquiv {k : ℕ} (D : Fin (k+1) → Type*) :
    (∀ s, D s) ≃ D 0 × (∀ s : Fin k, D s.succ) where
  toFun a := (a 0, fun s => a s.succ)
  invFun a := Fin.cons a.1 a.2
  left_inv := by
    intro a
    funext s
    refine Fin.cases ?_ (fun j => ?_) s <;> rfl
  right_inv := by intro a; rfl

omit [Fintype ι] [DecidableEq ι] in
theorem balanceBox_split {k : ℕ} (A : ι → ℤ) (C : Fin (k+1) → ℕ) :
    balanceBox A C ∘ (splitSlot k).symm =
      pairAssembly (balanceBox A (fun s => C s.succ)) (C 0) (C 0) := by
  funext i
  rcases i with (i | ⟨s,b⟩) | b
  · rfl
  · rfl
  · cases b <;> rfl

omit [Fintype ι] [DecidableEq ι] in
theorem balancedSlots_succ {k : ℕ}
    (f : (ι ⊕ (Fin (k+1) × Bool) → ℤ) → ℝ) (C : Fin (k+1) → ℕ) :
    balancedSlots f C = balancedSlots
      (balancedMarginal (fun q => f (q ∘ splitSlot k)) (C 0)) (fun s => C s.succ) := by
  funext p
  unfold balancedSlots
  rw [← Equiv.sum_comp (piHeadEquiv (fun s => Fin (C s+1))).symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [balancedMarginal, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext i
  rcases i with i | ⟨s,b⟩
  · rfl
  · refine Fin.cases ?_ (fun t => ?_) s <;> cases b <;> rfl

 

theorem balancedSlots_closure (k : ℕ) (f : (ι ⊕ (Fin k × Bool) → ℤ) → ℝ)
    (A : ι → ℤ) (C : Fin k → ℕ) (hC : ∀ s, 2 ≤ C s) (T : ℤ)
    (hp : PositiveSlice f (balanceBox A C) T)
    (hs : HasSignature f (balanceBox A C) T) :
    PositiveSlice (balancedSlots f C) A (T - ∑ s, (C s:ℤ)) ∧
    HasSignature (balancedSlots f C) A (T - ∑ s, (C s:ℤ)) := by
  induction k generalizing T with
  | zero =>
    let e : (ι ⊕ (Fin 0 × Bool)) ≃ ι := Equiv.sumEmpty _ _
    have hbox : balanceBox A C ∘ e.symm = A := by funext i; rfl
    have hf : balancedSlots f C = (fun p => f (p ∘ e)) := by
      funext p
      simp only [balancedSlots, Finset.univ_unique, Finset.sum_singleton]
      congr 1
      funext i
      rcases i with i | ⟨s,b⟩
      · rfl
      · exact Fin.elim0 s
    have hsum : (∑ s, (C s:ℤ)) = 0 := by simp
    rw [hsum, sub_zero, hf]
    simpa only [hbox] using And.intro (hp.reindex e) (hs.reindex e)
  | succ k ih =>
    rw [balancedSlots_succ]
    have hp' := hp.reindex (splitSlot k)
    have hs' := hs.reindex (splitSlot k)
    rw [balanceBox_split] at hp' hs'
    have hp'' := balancedMarginal_positive _ _ (C 0) T hp'
    have hs'' := balancedMarginal_signature _ _ (C 0) (hC 0) T hp' hs'
    have h := ih (balancedMarginal (fun q => f (q ∘ splitSlot k)) (C 0))
      (fun s => C s.succ) (fun s => hC s.succ) (T - (C 0:ℤ)) hp'' hs''
    rw [Fin.sum_univ_succ]
    convert h using 1 <;> ring_nf

end ManyBalanced

section SoftClosure
attribute [local instance] Classical.propDecidable
variable {m n k : ℕ} {ι κ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem softWeight_positive (η : ℝ) (hη : 0 < η)
    (r rb : Fin m → ℤ) (c cb : Fin n → ℤ) (B : Cell m n → ℤ)
    (small : Finset (Cell m n)) :
    PositiveSlice (softWeight η r rb c cb B small) (fun v => B v.2) (∑ s, B s) := by
  classical
  constructor
  · intro p hp ht
    simp only [softWeight]
    rw [ite_eq_left ⟨hp,ht⟩]
    exact pow_pos hη _
  · intro p hp
    simp only [softWeight, ite_eq_right hp]

 

theorem softWeight_context_balanced_signature
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
    (r rb : Fin m → ℤ) (c cb : Fin n → ℤ) (B : Cell m n → ℤ)
    (small : Finset (Cell m n))
    (e : Coordinate m n ≃ (κ ⊕ (ι ⊕ (Fin k × Bool))))
    (A : κ → ℤ) (D : ι → ℤ) (C : Fin k → ℕ) (hC : ∀ s, 2 ≤ C s)
    (he : (fun v => B v.2) ∘ e.symm = Sum.elim A (balanceBox D C))
    (σ : κ → ℤ) (hσ : InBox A σ) :
    let Φ := balancedSlots (fun p => softWeight η r rb c cb B small ((Sum.elim σ p) ∘ e)) C
    PositiveSlice Φ D ((∑ s, B s) - (∑ i, σ i) - ∑ s, (C s:ℤ)) ∧
    HasSignature Φ D ((∑ s, B s) - (∑ i, σ i) - ∑ s, (C s:ℤ)) := by
  have hp := (softWeight_positive η hη r rb c cb B small).reindex e
  have hs := (softWeight_signature η hη hη1 r rb c cb B small).reindex e
  rw [he] at hp hs
  exact balancedSlots_closure k _ D C hC _ (hp.fixedContext σ hσ) (hs.fixedContext σ hσ)

theorem softWeight_continuous (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) (p : Coordinate m n → ℤ) :
    Continuous (fun η : ℝ => softWeight η r rb c cb B small p) := by
  classical
  unfold softWeight
  split_ifs
  · fun_prop
  · fun_prop

 

theorem softWeight_zero (r rb : Fin m → ℤ) (c cb : Fin n → ℤ)
    (B : Cell m n → ℤ) (small : Finset (Cell m n)) (p : Coordinate m n → ℤ) :
    softWeight 0 r rb c cb B small p =
      if InBox (fun v => B v.2) p ∧ (∑ v, p v) = ∑ s, B s ∧
        softPenalty r rb c cb B small p = 0 then 1 else 0 := by
  classical
  unfold softWeight
  by_cases hb : InBox (fun v => B v.2) p ∧ (∑ v, p v) = ∑ s, B s
  · by_cases hd : softPenalty r rb c cb B small p = 0
    · simp [hb.1, hb.2, hd]
    · simp [hb.1, hb.2, hd, zero_pow hd]
  · simp only [ite_eq_right hb]
    symm
    apply ite_eq_right
    exact fun h => hb ⟨h.1,h.2.1⟩

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem balancedSoft_continuous
    (r rb : Fin m → ℤ) (c cb : Fin n → ℤ) (B : Cell m n → ℤ)
    (small : Finset (Cell m n))
    (e : Coordinate m n ≃ (κ ⊕ (ι ⊕ (Fin k × Bool))))
    (σ : κ → ℤ) (C : Fin k → ℕ) (p : ι → ℤ) :
    Continuous (fun η : ℝ => balancedSlots
      (fun q => softWeight η r rb c cb B small ((Sum.elim σ q) ∘ e)) C p) := by
  unfold balancedSlots
  apply continuous_finsetSum
  intro a _
  exact softWeight_continuous r rb c cb B small _

end SoftClosure

end Signature
end Contingency

end

end OAI
