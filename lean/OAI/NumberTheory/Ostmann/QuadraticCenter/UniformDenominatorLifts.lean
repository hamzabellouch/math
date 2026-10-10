import Mathlib.Combinatorics.Pigeonhole
import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterFromTuples

namespace OAI

/-! # Selecting one denominator for a large family of witnessed tuples -/

namespace Ostmann

open scoped BigOperators Classical

theorem exists_uniform_denominator_lifts (P : Finset ℕ) {k : ℕ}
    (E : Finset (Fin k ↪ P)) (Amax H : ℕ) (hAmax : 0 < Amax) (t : ℕ → ℤ)
    (hlift : ∀ e ∈ E, ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1) :
    ∃ a ∈ Finset.Icc 1 Amax, ∃ E' : Finset (Fin k ↪ P), E' ⊆ E ∧
      (E.card : ℝ) / Amax ≤ E'.card ∧
      ∀ e ∈ E', ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1 := by
  choose a ha h using fun e : E => hlift e.1 e.2
  let D := Finset.Icc 1 Amax
  let f : E → D := fun e => ⟨a e, ha e⟩
  let : Nonempty D := ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hAmax⟩⟩⟩
  have hcard : Fintype.card D = Amax := by simp [D]
  have hcount : Fintype.card D • ((E.card : ℝ) / Amax) ≤ (Fintype.card E : ℝ) := by
    rw [hcard, nsmul_eq_mul, Fintype.card_coe]
    have hA0 : (Amax : ℝ) ≠ 0 := by exact_mod_cast hAmax.ne'
    rw [mul_div_cancel₀ _ hA0]
  obtain ⟨d, hd⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card f hcount
  let T := (Finset.univ : Finset E).filter fun e => f e = d
  let E' := T.image Subtype.val
  have hE' : E' ⊆ E := by
    intro e he
    obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp he
    exact e'.2
  have hsize : (E.card : ℝ) / Amax ≤ (E'.card : ℝ) := by
    have hc : E'.card = T.card := Finset.card_image_of_injective _ Subtype.val_injective
    rw [hc]
    exact hd
  refine ⟨d.1, d.2, E', hE', hsize, ?_⟩
  intro e he
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
  have heq : a e' = d.1 := congrArg Subtype.val (Finset.mem_filter.mp he').2
  simpa only [heq] using h e'

/-- The common-center theorem applies to tuple-dependent denominators:
the finite pigeonhole loss is paid explicitly before the moment argument. -/
theorem exists_commonCenter_of_bounded_denominators (P : Finset ℕ)
    (t : ℕ → ℤ) (k d K H Z Amax : ℕ) (hd : d ≤ k + 1)
    (A V : ℝ) (hA : 0 < A) (hV : 0 < V) (hZ : 0 < Z) (hAmax : 0 < Amax)
    (hprime : ∀ p ∈ P, p.Prime) (hap : ∀ p ∈ P, Amax < p)
    (hmin : ∀ p ∈ P, Z ≤ p) (hlog : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hbudget : Real.log (2 * (H : ℝ)) < (K + 1 : ℕ) * V)
    (hsmall : 2 * K * (P.card : ℝ) ≤ A ^ 2)
    (E : Finset (Fin (k + 1) ↪ P))
    (hlift : ∀ e ∈ E, ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1),
        ∀ i, ((e i).1 : ℤ) ∣ n - (a : ℤ) * t (e i).1)
    (hpositive : 0 < (E.card : ℝ) / Amax -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z) :
    ∃ a ∈ Finset.Icc 1 Amax,
      ∃ n ∈ Finset.Ico (-(H : ℤ)) (H + 1), ∃ h : ℤ, ∃ m : ℕ,
        0 < m ∧ m ≤ Amax ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
        A ≤ ((matchingPrimes P a t n).card : ℝ) ∧
        (E.card : ℝ) / Amax - A ^ d * liftMomentUpper P.card (k + 1 - d) H Z ≤
          2 * P.card * ((matchingPrimes P a t n).card : ℝ) ^ k ∧
        ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
          let _ : Fact p.Prime := ⟨hprime p (Finset.mem_filter.mp hp).1⟩
          (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  obtain ⟨a, ha, E', _, hsize, hlift'⟩ :=
    exists_uniform_denominator_lifts P E Amax H hAmax t hlift
  have ha' := Finset.mem_Icc.mp ha
  have hpositive' : 0 < (E'.card : ℝ) -
      A ^ d * liftMomentUpper P.card (k + 1 - d) H Z := by linarith
  obtain ⟨n, hn, h, m, hm, hma, hcop, hbound, hlarge, hmoment, hcenters⟩ :=
    exists_commonCenter_of_tuple_lifts P a (by omega) t k d K H Z hd A V hA hV hZ
      hprime (fun p hp => ha'.2.trans_lt (hap p hp)) hmin hlog hbudget hsmall E' hlift' hpositive'
  exact ⟨a, ha, n, hn, h, m, hm, hma.trans ha'.2, hcop, hbound, hlarge,
    (by linarith), hcenters⟩

end Ostmann

end OAI
