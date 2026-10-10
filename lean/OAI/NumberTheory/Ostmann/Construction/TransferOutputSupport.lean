import OAI.NumberTheory.Ostmann.Construction.TransferFrequencyRange

namespace OAI

/-! # Coprimality and frequency units after the actual substitution -/

namespace Ostmann

/-- The common-prime obstruction is impossible once the derived output
frequency is smaller than every surviving prime. -/
theorem transfer_output_support (M L R Y V : ℕ) (v w s : ℤ)
    (hs : s ≠ 0) (hsV : s.natAbs ≤ V)
    (hrel : v * R - w * L = s * M)
    (hLY : L.Coprime Y) (hRY : R.Coprime Y)
    (hlargeL : ∀ q, q.Prime → q ∣ L → V < q)
    (hlargeR : ∀ q, q.Prime → q ∣ R → V < q)
    (hlargeY : ∀ q, q.Prime → q ∣ Y → V < q)
    (hunit : ∀ q, q.Prime → q ∣ L → q ∣ R → IsCoprime (q : ℤ) (M : ℤ)) :
    L.Coprime R ∧ L.Coprime Y ∧ R.Coprime Y ∧
      (L * R * Y).Coprime s.natAbs := by
  have hLR := transferred_products_coprime L R v w s M hs hrel
    (fun q hq hqL _ => hsV.trans_lt (hlargeL q hq hqL)) hunit
  have hL := large_prime_factors_coprime_frequency L s hs
    (fun q hq hqL => hsV.trans_lt (hlargeL q hq hqL))
  have hR := large_prime_factors_coprime_frequency R s hs
    (fun q hq hqR => hsV.trans_lt (hlargeR q hq hqR))
  have hY := large_prime_factors_coprime_frequency Y s hs
    (fun q hq hqY => hsV.trans_lt (hlargeY q hq hqY))
  exact ⟨hLR, hLY, hRY, (hL.mul_left hR).mul_left hY⟩

/-- In the integer extension, the inherited coprimality with the erased
pivot implies precisely the common-prime unit condition used above. -/
theorem common_prime_pivot_unit (M L R : ℕ) (hLM : L.Coprime M)
    (q : ℕ) (_hq : q.Prime) (hqL : q ∣ L) (_hqR : q ∣ R) :
    IsCoprime (q : ℤ) (M : ℤ) := by
  have hqM : q.Coprime M := hLM.coprime_dvd_left hqL
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa only [Int.gcd_natCast_natCast] using hqM)

theorem transfer_output_support_of_ranges (M L R Y B H V : ℕ)
    (hM : 0 < M) (v w s : ℤ) (hs : s ≠ 0)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B) (hL : L ≤ H) (hR : R ≤ H)
    (hscale : 2 * B * H ≤ V * M) (hrel : v * R - w * L = s * M)
    (hLM : L.Coprime M) (hLY : L.Coprime Y) (hRY : R.Coprime Y)
    (hlargeL : ∀ q, q.Prime → q ∣ L → V < q)
    (hlargeR : ∀ q, q.Prime → q ∣ R → V < q)
    (hlargeY : ∀ q, q.Prime → q ∣ Y → V < q) :
    s.natAbs ≤ V ∧ L.Coprime R ∧ L.Coprime Y ∧ R.Coprime Y ∧
      (L * R * Y).Coprime s.natAbs := by
  have hsV := transferred_frequency_bound M L R B H V s v w hM hv hw hL hR hscale hrel
  exact ⟨hsV, transfer_output_support M L R Y V v w s hs hsV hrel hLY hRY
    hlargeL hlargeR hlargeY (common_prime_pivot_unit M L R hLM)⟩

end Ostmann

end OAI
