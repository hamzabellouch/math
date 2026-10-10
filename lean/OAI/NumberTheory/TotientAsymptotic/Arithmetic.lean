import OAI.NumberTheory.TotientAsymptotic.Companion

namespace OAI

/-!
Arithmetic facts for the weighted companion theorem.  The inverse-fiber
transport is the elementary consequence used after Ford's propagation
construction (The distribution of totients, 2013 revision, Section 5,
equations (5.10)--(5.19), and Section 7.3).
-/

noncomputable section
open scoped BigOperators Topology

namespace TotientAsymptotic

lemma isTotient_eight : IsTotient 8 :=
  ⟨15, by decide, by decide⟩

lemma ell_eight : ell 8 = 15 := by
  have hle : ell 8 ≤ 15 := ell_le (by decide) (by decide)
  have hsmall : ∀ n ∈ Finset.range 15, n.totient ≠ 8 := by decide
  apply Nat.le_antisymm hle
  by_contra h
  exact hsmall (ell 8) (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
    (ell_spec isTotient_eight).2

theorem seed_one : ∃ d : ℕ, IsTotient d ∧ 1*d < ell d := by
  exact ⟨8, isTotient_eight, by rw [ell_eight]; norm_num⟩

lemma fk_le_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : fk k r ≤ 1 := by
  have hfirst : min 1 ((k+1 : ℝ) / r) ≤ 1 := min_le_left _ _
  have hsecond : 0 ≤ min 1 ((k : ℝ) / r) :=
    le_min zero_le_one (div_nonneg (Nat.cast_nonneg k) hr)
  unfold fk
  linarith

lemma fk_pos_iff (k : ℕ) {r : ℝ} (hr : 0 < r) : 0 < fk k r ↔ (k : ℝ) < r := by
  constructor
  · intro hf
    by_contra hk
    rw [fk_zero_of_le k hr (le_of_not_gt hk)] at hf
    exact (lt_irrefl (0 : ℝ)) hf
  · intro hk
    unfold fk
    rw [min_eq_right ((div_lt_one hr).mpr hk).le]
    apply sub_pos.mpr
    apply lt_min
    · exact (div_lt_one hr).mpr hk
    · exact (div_lt_div_iff_of_pos_right hr).mpr (by norm_num)

lemma fk_ell_pos_iff (k : ℕ) {d : ℕ} (hd : IsTotient d) :
    0 < fk k ((ell d : ℝ) / d) ↔ k*d < ell d := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (isTotient_pos hd)
  rw [fk_pos_iff k (lt_of_lt_of_le zero_lt_one (one_le_ell_ratio hd)),
    lt_div_iff₀ hdpos]
  norm_cast

lemma fk_eq_one_sub {k : ℕ} {r : ℝ} (hr : 0 < r)
    (hk : (k : ℝ) ≤ r) (hk1 : r ≤ k+1) : fk k r = 1 - k/r := by
  unfold fk
  rw [min_eq_left ((le_div_iff₀ hr).mpr (by simpa using hk1)),
    min_eq_right ((div_le_one hr).mpr hk)]

lemma fk_eq_inv {k : ℕ} {r : ℝ} (hr : 0 < r) (hk1 : (k+1 : ℝ) ≤ r) :
    fk k r = 1/r := by
  have hk : (k : ℝ) ≤ r := by linarith
  unfold fk
  rw [min_eq_right ((div_le_one hr).mpr hk1),
    min_eq_right ((div_le_one hr).mpr hk)]
  rw [← sub_div]
  congr 1
  ring

lemma fk_le_inv_succ (k : ℕ) {r : ℝ} (hr : 0 < r) :
    fk k r ≤ 1 / (k+1 : ℝ) := by
  have hkpos : (0 : ℝ) < k+1 := by positivity
  by_cases hk : r ≤ k
  · rw [fk_zero_of_le k hr hk]
    positivity
  have hkr : (k : ℝ) ≤ r := (lt_of_not_ge hk).le
  by_cases hk1 : r ≤ k+1
  · rw [fk_eq_one_sub hr hkr hk1]
    apply (le_div_iff₀ hkpos).mpr
    have hfrac : (k : ℝ) / (k+1) ≤ k/r :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg k) hr hk1
    have hid : (1 - (k : ℝ) / (k+1)) * (k+1) = 1 := by
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hkpos.ne']
      ring
    have hmul := mul_le_mul_of_nonneg_right hfrac hkpos.le
    nlinarith [hmul]
  · rw [fk_eq_inv hr (lt_of_not_ge hk1).le]
    exact one_div_le_one_div_of_le hkpos (lt_of_not_ge hk1).le

lemma N_le_V (k : ℕ) (x : ℝ) : N k x ≤ V x := by
  classical
  unfold N V
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, hvt, _⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv, hvt⟩

/-- The least preimage is preserved by a complete inverse-fiber dilation. -/
theorem ell_eq_mul_of_full_fiber {d v b : ℕ} (hd : IsTotient d) (_hb : 0 < b)
    (hfull : ∀ n : ℕ, (0 < n ∧ n.totient = v) ↔
      ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m) :
    ell v = b * ell d := by
  have he := ell_spec hd
  have hvpre : 0 < b * ell d ∧ (b * ell d).totient = v :=
    (hfull _).mpr ⟨ell d, he.1, he.2, rfl⟩
  have hv : IsTotient v := ⟨b * ell d, hvpre⟩
  apply le_antisymm (ell_le hvpre.1 hvpre.2)
  obtain ⟨m, hm, hmd, hvm⟩ := (hfull _).mp (ell_spec hv)
  rw [hvm]
  exact Nat.mul_le_mul_left b (ell_le hm hmd)

/-- Ford's full-fiber propagation cannot decrease the least-preimage ratio. -/
theorem ratio_le_of_full_fiber {d v b : ℕ} (hd : IsTotient d) (hb : 0 < b)
    (hv : v = d*b.totient)
    (hfull : ∀ n : ℕ, (0 < n ∧ n.totient = v) ↔
      ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m) :
    (ell d : ℝ) / d ≤ (ell v : ℝ) / v := by
  have hvpos : 0 < v := by
    rw [hv]
    exact Nat.mul_pos (isTotient_pos hd) (Nat.totient_pos.mpr hb)
  have hell := ell_eq_mul_of_full_fiber hd hb hfull
  have hcross : ell d * v ≤ ell v * d := by
    calc
      ell d * v = (ell d * d) * b.totient := by rw [hv]; ring
      _ ≤ (ell d * d) * b := Nat.mul_le_mul_left _ (Nat.totient_le b)
      _ = ell v * d := by rw [hell]; ring
  apply (div_le_div_iff₀ (Nat.cast_pos.mpr (isTotient_pos hd))
    (Nat.cast_pos.mpr hvpos)).mpr
  exact_mod_cast hcross

/-- Complete inverse-fiber dilations give distinct totients for distinct multipliers. -/
theorem mul_totient_injective_of_full_fibers {d b c : ℕ} (hd : IsTotient d)
    (hb : 0 < b) (hc : 0 < c)
    (hbfull : ∀ n : ℕ, (0 < n ∧ n.totient = d*b.totient) ↔
      ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m)
    (hcfull : ∀ n : ℕ, (0 < n ∧ n.totient = d*c.totient) ↔
      ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = c*m)
    (hvalue : d*b.totient = d*c.totient) : b = c := by
  apply Nat.eq_of_mul_eq_mul_right (ell_spec hd).1
  calc
    b * ell d = ell (d*b.totient) := (ell_eq_mul_of_full_fiber hd hb hbfull).symm
    _ = ell (d*c.totient) := congrArg ell hvalue
    _ = c * ell d := ell_eq_mul_of_full_fiber hd hc hcfull

theorem card_convenient_le_V {d : ℕ} (hd : IsTotient d) (S : Finset ℕ) (x : ℝ)
    (hS : ∀ b ∈ S, 0 < b ∧ d*b.totient ∈ Finset.Icc 1 ⌊x⌋₊ ∧
      ∀ n : ℕ, (0 < n ∧ n.totient = d*b.totient) ↔
        ∃ m : ℕ, 0 < m ∧ m.totient = d ∧ n = b*m) :
    (S.card : ℝ) ≤ V x := by
  classical
  have hinj : Set.InjOn (fun b : ℕ => d*b.totient) (S : Set ℕ) := by
    intro b hb c hc heq
    exact mul_totient_injective_of_full_fibers hd (hS b hb).1 (hS c hc).1
      (hS b hb).2.2 (hS c hc).2.2 heq
  have hsubset : S.image (fun b => d*b.totient) ⊆
      (Finset.Icc 1 ⌊x⌋₊).filter IsTotient := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have he := ell_spec hd
    have hw := ((hS b hb).2.2 (b*ell d)).mpr ⟨ell d, he.1, he.2, rfl⟩
    exact Finset.mem_filter.mpr ⟨(hS b hb).2.1, ⟨b*ell d, hw⟩⟩
  unfold V
  apply Nat.cast_le.mpr
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsubset

/-- The numerical least-preimage computation stated in the proof of Lemma 5.1
of Pollack--Pomerance--Treviño, *Sets of monotonicity for Euler's totient
function*, Ramanujan Journal 30 (2013), p. 9 of the author manuscript,
implies both seed cases of the weighted companion theorem. -/
theorem seeds_one_two_of_published_least_preimage
    (hseed : IsTotient (2^18 * 257))
    (hmin : ell (2^18 * 257) = 135268352) :
    (∃ d : ℕ, IsTotient d ∧ 1*d < ell d) ∧
    (∃ d : ℕ, IsTotient d ∧ 2*d < ell d) := by
  constructor
  · exact ⟨2^18 * 257, hseed, by rw [hmin]; norm_num⟩
  · exact ⟨2^18 * 257, hseed, by rw [hmin]; norm_num⟩

end TotientAsymptotic

end

end OAI
