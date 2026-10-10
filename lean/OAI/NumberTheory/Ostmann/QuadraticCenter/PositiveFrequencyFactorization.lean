import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeKernel

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem exists_squarefree_coprime_divisor_split {L a : ℕ}
    (hL : Squarefree L) (ha : Squarefree a) :
    ∃ s v : ℕ, Squarefree s ∧ s.Coprime L ∧ v ∣ L ∧ a = s * v := by
  refine ⟨a / a.gcd L, a.gcd L,
    ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a L)),
    Nat.coprime_div_gcd_of_squarefree ha hL.ne_zero, Nat.gcd_dvd_right a L, ?_⟩
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left a L)).symm

theorem exists_positive_frequency_factorization {L u : ℕ}
    (hL : Squarefree L) (hu : 0 < u) :
    ∃ s v w : ℕ, Squarefree s ∧ s.Coprime L ∧ v ∣ L ∧ 0 < w ∧ u = s * v * w ^ 2 := by
  obtain ⟨a, w, ha, hw, hprod, hsq⟩ := Nat.sq_mul_squarefree_of_pos hu
  obtain ⟨s, v, hs, hcop, hv, hsv⟩ := exists_squarefree_coprime_divisor_split hL hsq
  exact ⟨s, v, w, hs, hcop, hv, hw, by rw [← hprod, hsv]; ring⟩

theorem coprime_divisor_split_unique {L s v t z : ℕ}
    (hL : L ≠ 0) (hs : s.Coprime L) (ht : t.Coprime L)
    (hv : v ∣ L) (hz : z ∣ L) (heq : s * v = t * z) : s = t ∧ v = z := by
  have hvz : v = z := by
    rw [← Nat.gcd_mul_of_coprime_of_dvd hs hv, heq,
      Nat.gcd_mul_of_coprime_of_dvd ht hz]
  refine ⟨?_, hvz⟩
  rw [hvz] at heq
  exact mul_right_cancel₀ (Nat.pos_of_dvd_of_pos hz (Nat.pos_of_ne_zero hL)).ne' heq

theorem positive_frequency_factorization_unique {L s v w t z r : ℕ}
    (hL : Squarefree L) (hs : Squarefree s) (ht : Squarefree t)
    (hsc : s.Coprime L) (htc : t.Coprime L) (hv : v ∣ L) (hz : z ∣ L)
    (hw : 0 < w) (hr : 0 < r) (heq : s * v * w ^ 2 = t * z * r ^ 2) :
    s = t ∧ v = z ∧ w = r := by
  have hsv : Squarefree (s * v) := Nat.squarefree_mul_iff.mpr
    ⟨hsc.of_dvd_right hv, hs, hL.squarefree_of_dvd hv⟩
  have htz : Squarefree (t * z) := Nat.squarefree_mul_iff.mpr
    ⟨htc.of_dvd_right hz, ht, hL.squarefree_of_dvd hz⟩
  have h := QuadraticSieve.squarefree_square_decomposition_unique hw hr hsv htz
    (show w ^ 2 * (s * v) = r ^ 2 * (t * z) by simpa only [mul_comm] using heq)
  have hsplit := coprime_divisor_split_unique hL.ne_zero hsc htc hv hz h.2
  exact ⟨hsplit.1, hsplit.2, h.1⟩

abbrev PositiveFrequencyIndex (L : ℕ) :=
  {s : ℕ // Squarefree s ∧ s.Coprime L} × {v : ℕ // v ∣ L} × {w : ℕ // 0 < w}

def positiveFrequencyValue {L : ℕ} (t : PositiveFrequencyIndex L) : ℕ :=
  t.1.val * t.2.1.val * t.2.2.val ^ 2

noncomputable def positiveFrequencyEquiv {L : ℕ} (hL : Squarefree L) :
    PositiveFrequencyIndex L ≃ {u : ℕ // 0 < u} := by
  let f : PositiveFrequencyIndex L → {u : ℕ // 0 < u} := fun t =>
    ⟨positiveFrequencyValue t, mul_pos
      (mul_pos (Nat.pos_of_ne_zero t.1.property.1.ne_zero)
        (Nat.pos_of_dvd_of_pos t.2.1.property (Nat.pos_of_ne_zero hL.ne_zero)))
      (pow_pos t.2.2.property 2)⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    have h := positive_frequency_factorization_unique hL x.1.property.1 y.1.property.1
      x.1.property.2 y.1.property.2 x.2.1.property y.2.1.property
      x.2.2.property y.2.2.property (congrArg Subtype.val hxy)
    exact Prod.ext (Subtype.ext h.1) (Prod.ext (Subtype.ext h.2.1) (Subtype.ext h.2.2))
  · intro u
    obtain ⟨s, v, w, hs, hc, hv, hw, heq⟩ := exists_positive_frequency_factorization hL u.property
    exact ⟨(⟨s, hs, hc⟩, ⟨v, hv⟩, ⟨w, hw⟩), Subtype.ext heq.symm⟩

@[simp] theorem positiveFrequencyEquiv_apply {L : ℕ} (hL : Squarefree L)
    (t : PositiveFrequencyIndex L) :
    (positiveFrequencyEquiv hL t).val = positiveFrequencyValue t := rfl

theorem tsum_positive_frequency_reindex {L : ℕ} (hL : Squarefree L) (F : ℕ → ℂ) :
    (∑' u : {u : ℕ // 0 < u}, F u.val) =
      ∑' t : PositiveFrequencyIndex L, F (positiveFrequencyValue t) :=
  ((positiveFrequencyEquiv hL).tsum_eq (fun u => F u.val)).symm

end Ostmann.QuadraticCenter

end

end OAI
