import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProofSplitting

namespace OAI

/-! Exact fibers above split rational primes, and the quadratic-norm remainder. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_intCast (a : ℤ) : normNat (a : Eisenstein) = a.natAbs ^ 2 := by
  apply Nat.cast_injective (R := ℝ)
  rw [normNat_cast]
  change Complex.normSq (a : ℂ) = _
  rw [Nat.cast_pow, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  simp [Complex.normSq_apply, pow_two]

lemma primaryPrime_ne_conjugate_of_prime_norm {z : Eisenstein}
    (hn : (normNat z).Prime) : z ≠ conjugate z := by
  intro he
  obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
  change (normNat (ofCoords a b)).Prime at hn
  change ofCoords a b = conjugate (ofCoords a b) at he
  have him := congrArg (fun w : Eisenstein => (w : ℂ).im) he
  simp only [ofCoords_coe, conjugate_coe, Complex.star_def, Complex.conj_im, Complex.add_im,
    Complex.intCast_im, Complex.mul_im, Complex.intCast_re, zero_mul,
    add_zero, zero_add, omega_im] at him
  have hb : b = 0 := by
    have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have : (b : ℝ) = 0 := by nlinarith
    exact_mod_cast this
  subst b
  have heq : ofCoords a 0 = (a : Eisenstein) := by simp [ofCoords]
  rw [heq, normNat_intCast] at hn
  exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2) hn

lemma pnt_primaryPrime_eq_or_conjugate_of_norm_eq {z w : Eisenstein}
    (hz : primaryPrime z) (hw : primaryPrime w) (hn : normNat w = normNat z) :
    w = z ∨ w = conjugate z := by
  have hd : w ∣ z * conjugate z := by
    rw [← normNat_cast_eq_mul_conjugate, ← hn, normNat_cast_eq_mul_conjugate]
    exact dvd_mul_right _ _
  rcases hw.2.dvd_or_dvd hd with h | h
  · exact Or.inl (primary_associated_eq hw.1 hz.1
      (hw.2.associated_of_dvd hz.2 h))
  · exact Or.inr (primary_associated_eq hw.1 (primary_conjugate hz.1)
      (hw.2.associated_of_dvd (primaryPrime_conjugate hz).2 h))

lemma primaryPrime_normFiber_card_le_two (X : ℝ) (n : ℕ) :
    ((primeCutoff X).filter (fun z => normNat z = n)).card ≤ 2 := by
  let S := (primeCutoff X).filter (fun z => normNat z = n)
  change S.card ≤ 2
  by_cases hs : S.Nonempty
  · obtain ⟨z,hz⟩ := hs
    have hzP := (mem_primeCutoff.mp (Finset.mem_filter.mp hz).1).1
    have hsub : S ⊆ {z, conjugate z} := by
      intro w hw
      have hwP := (mem_primeCutoff.mp (Finset.mem_filter.mp hw).1).1
      have hn := (Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm
      rcases pnt_primaryPrime_eq_or_conjugate_of_norm_eq hzP hwP hn with h | h
      · simp [h]
      · simp [h]
    apply (Finset.card_le_card hsub).trans
    by_cases h : z = conjugate z
    · rw [← h]
      simp
    · rw [Finset.card_pair h]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- Exactly two primary primes lie above each split rational prime. -/
theorem primaryPrime_normFiber_card_eq_two {p : ℕ} (hp : p.Prime)
    (hmod : p % 3 = 1) {X : ℝ} (hpX : (p : ℝ) ≤ X) :
    ((primeCutoff X).filter (fun z => normNat z = p)).card = 2 := by
  obtain ⟨z,hz,hn⟩ := exists_primaryPrime_norm_of_mod_one hp hmod
  have hne := primaryPrime_ne_conjugate_of_prime_norm (hn ▸ hp)
  have he : (primeCutoff X).filter (fun w => normNat w = p) = {z,conjugate z} := by
    ext w
    simp only [Finset.mem_filter, mem_primeCutoff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hw
      exact pnt_primaryPrime_eq_or_conjugate_of_norm_eq hz hw.1.1 (hw.2.trans hn.symm)
    · intro hw
      rcases hw with rfl | rfl
      · exact ⟨⟨hz, by rwa [← normNat_cast, hn]⟩, hn⟩
      · exact ⟨⟨primaryPrime_conjugate hz, by rwa [norm_conjugate, ← normNat_cast, hn]⟩,
          by simpa using hn⟩
  rw [he, Finset.card_pair hne]

/-- Every other norm is the square of a rational prime. -/
lemma primaryPrime_norm_square_of_not_prime {z : Eisenstein} (hz : primaryPrime z)
    (hn : ¬ (normNat z).Prime) :
    ∃ p : ℕ, p.Prime ∧ normNat z = p ^ 2 := by
  obtain ⟨p,hp,_hd,hshape⟩ := primaryPrime_rational_below hz
  exact ⟨p,hp,hshape.resolve_left (fun h => hn (h ▸ hp))⟩

end CubicFirstMoment

end

end OAI
