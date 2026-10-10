import Mathlib

namespace OAI

namespace Ostmann.QuadraticSieve

open scoped ArithmeticFunction.Moebius

theorem isSquare_mul_iff_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    IsSquare (m * n) ↔ IsSquare m ∧ IsSquare n := by
  constructor
  · rintro ⟨r, hr⟩
    have hu : IsUnit (gcd m n) := by simpa only [Nat.isUnit_iff, gcd_eq_nat_gcd] using hmn
    obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu (show m * n = r ^ 2 by simpa [sq] using hr)
    obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (show IsUnit (gcd n m) by simpa [gcd_comm] using hu)
      (show n * m = r ^ 2 by simpa [sq, mul_comm] using hr)
    exact ⟨⟨a, by simpa [sq] using ha⟩, ⟨b, by simpa [sq] using hb⟩⟩
  · exact fun h => h.1.mul h.2

noncomputable def squareLift (f : ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if IsSquare n then f n.sqrt else 0, by simp⟩

@[simp] theorem squareLift_apply_sq (f : ArithmeticFunction ℤ) (n : ℕ) :
    squareLift f (n ^ 2) = f n := by
  simp [squareLift, show IsSquare (n ^ 2) from ⟨n, by ring⟩]

@[simp] theorem squareLift_apply_of_not_square (f : ArithmeticFunction ℤ) {n : ℕ}
    (hn : ¬ IsSquare n) : squareLift f n = 0 := by simp [squareLift, hn]

theorem squareLift_isMultiplicative {f : ArithmeticFunction ℤ} (hf : f.IsMultiplicative) :
    (squareLift f).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · change squareLift f (1 ^ 2) = 1
    rw [squareLift_apply_sq]
    exact hf.1
  intro m n hmn
  by_cases hm : IsSquare m
  · by_cases hn : IsSquare n
    · obtain ⟨a, rfl⟩ := hm
      obtain ⟨b, rfl⟩ := hn
      have hab : a.Coprime b :=
        (hmn.of_dvd_left (dvd_mul_right a a)).of_dvd_right (dvd_mul_right b b)
      rw [show (a * a) * (b * b) = (a * b) ^ 2 by ring,
        squareLift_apply_sq, show a * a = a ^ 2 from (sq a).symm,
        show b * b = b ^ 2 from (sq b).symm, squareLift_apply_sq, squareLift_apply_sq]
      exact hf.2 hab
    · have hmn' : ¬ IsSquare (m * n) := fun h => hn ((isSquare_mul_iff_of_coprime hmn).mp h).2
      simp [squareLift_apply_of_not_square _ hn, squareLift_apply_of_not_square _ hmn']
  · have hmn' : ¬ IsSquare (m * n) := fun h => hm ((isSquare_mul_iff_of_coprime hmn).mp h).1
    simp [squareLift_apply_of_not_square _ hm, squareLift_apply_of_not_square _ hmn']

noncomputable def divisorMoebius (Δ : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ∣ Δ then μ n else 0, by simp⟩

@[simp] theorem divisorMoebius_apply (Δ n : ℕ) :
    divisorMoebius Δ n = if n ∣ Δ then μ n else 0 := rfl

theorem divisorMoebius_isMultiplicative (Δ : ℕ) : (divisorMoebius Δ).IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hmn
  have hdiv : m * n ∣ Δ ↔ m ∣ Δ ∧ n ∣ Δ :=
    ⟨fun h => ⟨(dvd_mul_right m n).trans h, (dvd_mul_left n m).trans h⟩,
      fun h => hmn.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  simp only [divisorMoebius_apply, ArithmeticFunction.isMultiplicative_moebius.2 hmn, hdiv]
  by_cases hm : m ∣ Δ <;> by_cases hn : n ∣ Δ <;> simp [hm, hn]

noncomputable def squarefreeIndicator : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius

@[simp] theorem squarefreeIndicator_apply (n : ℕ) :
    squarefreeIndicator n = if Squarefree n then 1 else 0 := by
  simpa only [squarefreeIndicator, ArithmeticFunction.pmul_apply, ← sq] using
    (ArithmeticFunction.moebius_sq (n := n))

theorem squarefreeIndicator_isMultiplicative : squarefreeIndicator.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.pmul ArithmeticFunction.isMultiplicative_moebius

noncomputable def coprimeSquarefreeIndicator (Δ : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n.Coprime Δ then squarefreeIndicator n else 0, by simp⟩

@[simp] theorem coprimeSquarefreeIndicator_apply (Δ n : ℕ) :
    coprimeSquarefreeIndicator Δ n = if Squarefree n ∧ n.Coprime Δ then 1 else 0 := by
  change (if n.Coprime Δ then squarefreeIndicator n else 0) = _
  by_cases hc : n.Coprime Δ
  · rw [ite_eq_left hc, squarefreeIndicator_apply]
    by_cases hs : Squarefree n
    · rw [ite_eq_left hs, ite_eq_left ⟨hs, hc⟩]
    · rw [ite_eq_right hs, ite_eq_right (fun h => hs h.1)]
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.2)]

theorem coprimeSquarefreeIndicator_isMultiplicative (Δ : ℕ) :
    (coprimeSquarefreeIndicator Δ).IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hmn
  change (if (m * n).Coprime Δ then squarefreeIndicator (m * n) else 0) =
    (if m.Coprime Δ then squarefreeIndicator m else 0) *
      (if n.Coprime Δ then squarefreeIndicator n else 0)
  rw [squarefreeIndicator_isMultiplicative.2 hmn]
  by_cases hm : m.Coprime Δ
  · by_cases hn : n.Coprime Δ
    · rw [ite_eq_left hm, ite_eq_left hn, ite_eq_left (Nat.coprime_mul_iff_left.mpr ⟨hm, hn⟩)]
    · rw [ite_eq_left hm, ite_eq_right hn,
        ite_eq_right (fun h => hn (Nat.coprime_mul_iff_left.mp h).2), mul_zero]
  · rw [ite_eq_right hm, ite_eq_right (fun h => hm (Nat.coprime_mul_iff_left.mp h).1), zero_mul]

end Ostmann.QuadraticSieve

end OAI
