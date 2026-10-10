import OAI.NumberTheory.Ostmann.Construction.BalancedHalfInitialStatistic
import OAI.NumberTheory.Ostmann.Construction.InitialCutoffProduct
import OAI.NumberTheory.Ostmann.Construction.SupportedRegularInitialAmplitude

namespace OAI

/-! # Repeated-prime removal for the selected two-cutoff initial statistic -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem balanced_half_initial_amplitude
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (b d r m : ℕ) (Tb Td : ℝ)
    (μ₀ : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (hμ₀ : ∀ q, 0 ≤ μ₀ q) (hμb : ∀ i q, 0 ≤ μb i q) (hμd : ∀ i q, 0 ≤ μd i q) (hμc : ∀ i q, 0 ≤ μc i q)
    (hm : 1 ≤ m) (hb : b ≤ m) (hd : d ≤ m) (hTb : Tb ≤ m) (hTd : Td ≤ m)
    (hlogb : ∀ i (q : P), μb i q ≠ 0 → Real.log (q : ℝ) ≤ Real.exp Tb)
    (hlogd : ∀ i (q : P), μd i q ≠ 0 → Real.log (q : ℝ) ≤ Real.exp Td)
    (hmb : ∀ i, (1 / 2 : ℝ) ≤ ∑ q, if (1 / 3 : ℝ) ≤ residueDensity (S q) ∧
      residueDensity (S q) ≤ 2 / 3 then μb i q else 0)
    (hmd : ∀ i, (1 / 2 : ℝ) ≤ ∑ q, if (1 / 3 : ℝ) ≤ residueDensity (S q) ∧
      residueDensity (S q) ≤ 2 / 3 then μd i q else 0)
    (hmc : ∀ i, ∑ q, μc i q = 1)
    (hgc : ∀ i q, μc i q ≠ 0 → (1 / 3 : ℝ) ≤ residueDensity (S q) ∧ residueDensity (S q) ≤ 2 / 3)
    (E : Finset ℤ) (δ c : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hendpoint : ∀ a ∈ E, ∀ q : P, (a : ZMod (q : ℕ)) ∈ S q)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E,
      (∑ q : P, (μ₀ q : ℂ) * primePhysicalTest (S q) true (favorable q)
        (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re)
    (C : Fin ((b + (d + r)) + 1) → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (q : P), (q : ℝ) *
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) :
        Fin ((b + (d + r)) + 1) → P → ℝ) i q ≤ C i)
    (H R Δ η : ℝ) (hR : 0 < R) (N : ℕ)
    (hsupp : ∀ t : ℝ, H < |t| → 𝓕 ψ t = 0)
    (hsmall : ∀ i (q : P),
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) :
        Fin ((b + (d + r)) + 1) → P → ℝ) i q ≠ 0 → H * R < (q : ℝ))
    (hcut : ∀ cb ∈ Finset.Icc (0 : ℤ) ⌈(b : ℝ) * Real.exp Tb⌉₊,
      ∀ cd ∈ Finset.Icc (0 : ℤ) ⌈(d : ℝ) * Real.exp Td⌉₊,
      ∀ x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P,
        productPrior (Fin.append
          (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
          (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0 →
        doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
          (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0 →
        H * (∏ i, (x i : ℕ)) ≤ N * X)
    (hlower : ∀ cb ∈ Finset.Icc (0 : ℤ) ⌈(b : ℝ) * Real.exp Tb⌉₊,
      ∀ cd ∈ Finset.Icc (0 : ℤ) ⌈(d : ℝ) * Real.exp Td⌉₊,
      ∀ x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P,
        productPrior (Fin.append
          (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
          (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0 →
        doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
          (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0 →
        X * Real.exp Δ ≤ ∏ i, (x i : ℝ))
    (hupper : ∀ cb ∈ Finset.Icc (0 : ℤ) ⌈(b : ℝ) * Real.exp Tb⌉₊,
      ∀ cd ∈ Finset.Icc (0 : ℤ) ⌈(d : ℝ) * Real.exp Td⌉₊,
      ∀ x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P,
        productPrior (Fin.append
          (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))
          (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)))) x ≠ 0 →
        doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
          (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)) x ≠ 0 →
        (∏ i, (x i : ℝ)) ≤ X * R)
    (hscale : Real.sqrt X * (η + ‖𝓕 ψ 0‖ * (∏ i, Fin.append C C i) *
      ((((b + (d + r)) + 1) + ((b + (d + r)) + 1) : ℕ) : ℝ) ^
        (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) *
      Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
        (E.card : ℝ) * (c * (Real.exp (-(2 * (Real.log 2 + 2)) * m) *
          (1 / 2 : ℝ) ^ (b + (d + r)) * δ) ^ 2)) :
    ∃ cb ∈ Finset.Icc (0 : ℤ) ⌈(b : ℝ) * Real.exp Tb⌉₊,
    ∃ cd ∈ Finset.Icc (0 : ℤ) ⌈(d : ℝ) * Real.exp Td⌉₊,
      let ν : Fin ((b + (d + r)) + 1) → P → ℝ := Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))
      let F : Fin ((b + (d + r)) + 1) → (q : P) → ZMod (q : ℕ) → ℂ :=
        primeHalfTests P S favorable
      let W := doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
        (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ))
      η ≤ ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ X N W‖ := by
  obtain ⟨cb, hcb, cd, hcd, hstat⟩ := balanced_half_initial_statistic P hP S favorable
    b d r m Tb Td μ₀ μb μd μc hμb hμd hμc hm hb hd hTb hTd hlogb hlogd
    hmb hmd hmc hgc E δ c hδ hc hendpoint hmean ψ X hX hψ hcE
  refine ⟨cb, hcb, cd, hcd, ?_⟩
  dsimp only
  let ν : Fin ((b + (d + r)) + 1) → P → ℝ := Fin.cons μ₀ (Fin.append μb (Fin.append μd μc))
  let F : Fin ((b + (d + r)) + 1) → (q : P) → ZMod (q : ℕ) → ℂ :=
    primeHalfTests P S favorable
  let W := doubledHalfWeight (fun y : Fin ((b + (d + r)) + 1) → P =>
    (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ))
  have hν (i : Fin ((b + (d + r)) + 1)) (q : P) : 0 ≤ ν i q := by
    refine Fin.cases (hμ₀ q) (fun j => ?_) i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [ν, Fin.cons_succ, Fin.append_left] using hμb j q
    · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
      · simpa only [ν, Fin.cons_succ, Fin.append_right, Fin.append_left] using hμd t q
      · simpa only [ν, Fin.cons_succ, Fin.append_right] using hμc t q
  have hW (x : Fin (((b + (d + r)) + 1) + ((b + (d + r)) + 1)) → P) : ‖W x‖ ≤ 1 := by
    have hh (y : Fin ((b + (d + r)) + 1) → P) :
        ‖(initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d r cb cd (Fin.tail y) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (initialHalfCutoffWeight_nonneg _ _ _ _ _ _ _)]
      exact initialHalfCutoffWeight_le_one _ _ _ _ _ _ _
    change ‖(_ : ℂ) * _‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (hh _) (hh _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact regularInitialAmplitude_lower_on_support P hP (Fin.append ν ν) (Fin.append C C)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left] using hν j q)
      (fun j => by simpa only [Fin.append_right] using hν j q) i)
    (fun i => Fin.addCases (fun j => by simpa only [Fin.append_left] using hC j)
      (fun j => by simpa only [Fin.append_right] using hC j) i)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, ν] using hbound j q)
      (fun j => by simpa only [Fin.append_right, ν] using hbound j q) i)
    (Fin.append F F)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, F] using
      (primeHalfTests_sum (n := b + (d + r)) P S favorable j q))
      (fun j => by simpa only [Fin.append_right, F] using
        (primeHalfTests_sum (n := b + (d + r)) P S favorable j q)) i)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, F] using
      (primeHalfTests_energy (n := b + (d + r)) P S favorable j q))
      (fun j => by simpa only [Fin.append_right, F] using
        (primeHalfTests_energy (n := b + (d + r)) P S favorable j q)) i)
    ψ X H R Δ η hX hR N W hW (hcut cb hcb cd hcd) hsupp
    (fun i q => Fin.addCases
      (fun j hj => hsmall j q (by simpa only [Fin.append_left, ν] using hj))
      (fun j hj => hsmall j q (by simpa only [Fin.append_right, ν] using hj)) i)
    (hlower cb hcb cd hcd) (hupper cb hcb cd hcd) (hscale.trans hstat)

end Ostmann

end OAI
