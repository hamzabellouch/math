import OAI.NumberTheory.Ostmann.QuadraticSieveMainCancellationLocal

namespace OAI

namespace Ostmann.QuadraticSieve

open scoped ArithmeticFunction.Moebius

lemma sq_sqrt_of_isSquare {n : ℕ} (hn : IsSquare n) : n.sqrt ^ 2 = n := by
  obtain ⟨a, rfl⟩ := hn
  simp [sq]

theorem squareLift_mul_apply (f g : ArithmeticFunction ℤ) {w : ℕ} (hw : w ≠ 0) :
    (squareLift f * g) w =
      ∑ u ∈ w.divisors, if u ^ 2 ∣ w then f u * g (w / u ^ 2) else 0 := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => squareLift f a * g b)]
  calc
    _ = ∑ x ∈ w.divisors.filter IsSquare, f x.sqrt * g (w / x) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hs : IsSquare x <;> simp [squareLift, hs]
    _ = ∑ u ∈ w.divisors.filter (fun u => u ^ 2 ∣ w), f u * g (w / u ^ 2) := by
      apply Finset.sum_bij (fun x hx => x.sqrt)
      · intro x hx
        obtain ⟨hxw, hxs⟩ := Finset.mem_filter.mp hx
        have heq := sq_sqrt_of_isSquare hxs
        have hsq : x.sqrt ^ 2 ∣ w := by
          rw [heq]
          exact (Nat.mem_divisors.mp hxw).1
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
          ⟨(dvd_pow_self x.sqrt (by decide)).trans hsq, hw⟩, hsq⟩
      · intro x hx y hy hxy
        have hxs := sq_sqrt_of_isSquare (Finset.mem_filter.mp hx).2
        have hys := sq_sqrt_of_isSquare (Finset.mem_filter.mp hy).2
        rw [← hxs, ← hys, hxy]
      · intro u hu
        have hsq := (Finset.mem_filter.mp hu).2
        refine ⟨u ^ 2, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hsq, hw⟩,
          ⟨u, by ring⟩⟩, ?_⟩
        exact Nat.sqrt_eq' u
      · intro x hx
        rw [sq_sqrt_of_isSquare (Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_filter _ _

noncomputable def mainAlpha (Δ w : ℕ) : ℤ :=
  ∑ e ∈ Δ.divisors, if e ∣ w ∧ Squarefree (w / e) then μ e else 0

noncomputable def mainBeta (Δ w : ℕ) : ℤ :=
  ∑ u ∈ Δ.divisors,
    if u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧ (w / u ^ 2).Coprime Δ then μ u else 0

theorem mainAlpha_eq_function {Δ : ℕ} (hΔ : Δ ≠ 0) (w : ℕ) :
    mainAlpha Δ w = mainAlphaFunction Δ w := by
  by_cases hw : w = 0
  · simp [hw, mainAlpha]
  have hsets : w.divisors.filter (fun e => e ∣ Δ) = Δ.divisors.filter (fun e => e ∣ w) := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hew, _⟩, heΔ⟩
      exact ⟨⟨heΔ, hΔ⟩, hew⟩
    · rintro ⟨⟨heΔ, _⟩, hew⟩
      exact ⟨⟨hew, hw⟩, heΔ⟩
  symm
  rw [mainAlphaFunction, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun e b => divisorMoebius Δ e * squarefreeIndicator b)]
  calc
    _ = ∑ e ∈ w.divisors.filter (fun e => e ∣ Δ), μ e * squarefreeIndicator (w / e) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hd : e ∣ Δ <;> simp [hd]
    _ = ∑ e ∈ Δ.divisors.filter (fun e => e ∣ w), μ e * squarefreeIndicator (w / e) := by rw [hsets]
    _ = _ := by
      rw [Finset.sum_filter]
      unfold mainAlpha
      apply Finset.sum_congr rfl
      intro e he
      by_cases hew : e ∣ w <;> by_cases hsf : Squarefree (w / e) <;> simp [hew, hsf]

theorem mainBeta_eq_function {Δ : ℕ} (hΔ : Δ ≠ 0) (w : ℕ) :
    mainBeta Δ w = mainBetaFunction Δ w := by
  by_cases hw : w = 0
  · simp [hw, mainBeta]
  have hsets : w.divisors.filter (fun u => u ^ 2 ∣ w ∧ u ∣ Δ) =
      Δ.divisors.filter (fun u => u ^ 2 ∣ w) := by
    ext u
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hsq, huΔ⟩
      exact ⟨⟨huΔ, hΔ⟩, hsq⟩
    · rintro ⟨⟨huΔ, _⟩, hsq⟩
      exact ⟨⟨(dvd_pow_self u (by decide)).trans hsq, hw⟩, hsq, huΔ⟩
  symm
  rw [mainBetaFunction, squareLift_mul_apply _ _ hw]
  calc
    _ = ∑ u ∈ w.divisors.filter (fun u => u ^ 2 ∣ w ∧ u ∣ Δ),
        μ u * coprimeSquarefreeIndicator Δ (w / u ^ 2) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hsq : u ^ 2 ∣ w <;> by_cases huΔ : u ∣ Δ <;> simp [hsq, huΔ]
    _ = ∑ u ∈ Δ.divisors.filter (fun u => u ^ 2 ∣ w),
        μ u * coprimeSquarefreeIndicator Δ (w / u ^ 2) := by rw [hsets]
    _ = _ := by
      rw [Finset.sum_filter]
      unfold mainBeta
      apply Finset.sum_congr rfl
      intro u hu
      rw [coprimeSquarefreeIndicator_apply]
      by_cases hsq : u ^ 2 ∣ w
      · rw [ite_eq_left hsq]
        by_cases hs : Squarefree (w / u ^ 2) ∧ (w / u ^ 2).Coprime Δ
        · rw [ite_eq_left hs, ite_eq_left ⟨hsq, hs⟩, mul_one]
        · rw [ite_eq_right hs, ite_eq_right (fun h => hs h.2), mul_zero]
      · rw [ite_eq_right hsq, ite_eq_right (fun h => hsq h.1)]

theorem mainAlpha_eq_mainBeta {Δ : ℕ} (hΔ : Δ ≠ 0) (w : ℕ) :
    mainAlpha Δ w = mainBeta Δ w := by
  rw [mainAlpha_eq_function hΔ, mainBeta_eq_function hΔ, mainAlphaFunction_eq_mainBetaFunction]

theorem mainAlpha_eq_mainBeta_of_squarefree {Δ : ℕ} (hΔ : Squarefree Δ) (w : ℕ) :
    mainAlpha Δ w = mainBeta Δ w := mainAlpha_eq_mainBeta hΔ.ne_zero w

end Ostmann.QuadraticSieve

end OAI
