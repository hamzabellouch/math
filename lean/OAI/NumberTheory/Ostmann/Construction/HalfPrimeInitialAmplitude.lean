import OAI.NumberTheory.Ostmann.Construction.HalfPrimeEndpoint

namespace OAI

/-! # The positive statistic for the actual phase/residue half-list -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def primeHalfTests {n : ℕ} (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool) :
    Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ :=
  Fin.cons (fun q => primePhysicalTest (S q) true (favorable q))
    (fun _ q => normalizedResidueIndicator (S q))

theorem primeHalfTests_sum {n : ℕ} (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (i : Fin (n + 1)) (q : P) : (∑ a, primeHalfTests P S favorable i q a) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact primePhysicalTest_sum (S q) true (favorable q)
  · exact normalizedResidueIndicator_sum (S q)

theorem primeHalfTests_energy {n : ℕ} (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (i : Fin (n + 1)) (q : P) : (∑ a, ‖primeHalfTests P S favorable i q a‖ ^ 2) ≤ q := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact primePhysicalTest_energy (S q) true (favorable q)
  · exact normalizedResidueIndicator_energy_le (S q)

/-- This is (7.5) before the asymptotic constants are absorbed: the only
mean premise is the selected actual giant mean, and the nongiant factors
are the manuscript's exact normalized residue indicators. -/
theorem primeHalfTests_statistic_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (μ₀ : P → ℝ) (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ)
    (hμ : ∀ i q, 0 ≤ μ i q) (hw : ∀ x, 0 ≤ w x)
    (E : Finset ℤ) (B : Finset (Fin n → P)) (β δ c : ℝ)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hmass : β ≤ ∑ x ∈ B, productPrior μ x * w x)
    (hbalance : ∀ x ∈ B, ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S (x i)) ∧
      residueDensity (S (x i)) ≤ 2 / 3)
    (hendpoint : ∀ a ∈ E, ∀ q : P, (a : ZMod (q : ℕ)) ∈ S q)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E,
      (∑ q : P, (μ₀ q : ℂ) * primePhysicalTest (S q) true (favorable q)
        (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    let ν := Fin.cons μ₀ μ
    let F : Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
    let W := fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ)
    (E.card : ℝ) * (c * (β * (1 / 2 : ℝ) ^ n * δ) ^ 2) ≤
      ‖∑ x : Fin ((n + 1) + (n + 1)) → P,
        (productPrior (Fin.append ν ν) x : ℂ) * doubledHalfWeight W x *
          physicalTupleSum P x (Fin.append F F) ψ X‖ := by
  let : ∀ q : P, Fact (q : ℕ).Prime := fun q => ⟨hP q q.property⟩
  exact halfPrimeMean_giant_endpoint_lower P μ₀ μ
    (fun q => primePhysicalTest (S q) true (favorable q))
    (fun _ q => normalizedResidueIndicator (S q)) w
    (fun _ q => endpointResidueValue (S q)) hμ hw
    (fun _ q => endpointResidueValue_nonneg (S q))
    (fun q a => primePhysicalTest_real (S q) true (favorable q) a)
    (fun _ _ _ => Complex.ofReal_im _) E B β (1 / 2) δ c hβ (by norm_num) hδ hc
    hmass (fun x hx i => endpointResidueValue_balanced (S (x i))
      (hbalance x hx i).1 (hbalance x hx i).2)
    (fun a ha _ q => normalizedResidueIndicator_endpoint (S q) _ (hendpoint a ha q))
    hmean ψ X hX hψ hcE

/-- The endpoint construction gives the Fourier lower bound. The error allowance is the proved repeated-prime bound under the
original mixed marginals. -/
theorem primeHalfTests_initialAmplitude_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (hP : ∀ q ∈ P, q.Prime)
    (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
    (ν : Fin (n + 1) → P → ℝ) (C : Fin (n + 1) → ℝ)
    (hν : ∀ i q, 0 ≤ ν i q) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (q : P), (q : ℝ) * ν i q ≤ C i)
    (w : (Fin n → P) → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (E : Finset ℤ) (B : Finset (Fin n → P)) (β δ c : ℝ)
    (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hmass : β ≤ ∑ x ∈ B, productPrior (Fin.tail ν) x * w x)
    (hbalance : ∀ x ∈ B, ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S (x i)) ∧
      residueDensity (S (x i)) ≤ 2 / 3)
    (hendpoint : ∀ a ∈ E, ∀ q : P, (a : ZMod (q : ℕ)) ∈ S q)
    (hmean : (E.card : ℝ) * δ ≤ ∑ a ∈ E,
      (∑ q : P, (ν 0 q : ℂ) * primePhysicalTest (S q) true (favorable q)
        (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X H R Δ η : ℝ) (hX : 0 < X) (hR : 0 < R) (N : ℕ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    let F : Fin (n + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
    let W := doubledHalfWeight (fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ))
    (∀ x, W x ≠ 0 → H * (∏ i, (x i : ℕ)) ≤ N * X) →
    (∀ t : ℝ, H < |t| → 𝓕 ψ t = 0) →
    (∀ p : P, H * R < (p : ℝ)) →
    (∀ x, W x ≠ 0 → X * Real.exp Δ ≤ ∏ i, (x i : ℝ)) →
    (∀ x, W x ≠ 0 → (∏ i, (x i : ℝ)) ≤ X * R) →
    Real.sqrt X * (η + ‖𝓕 ψ 0‖ * (∏ i, Fin.append C C i) *
      (((n + 1) + (n + 1) : ℕ) : ℝ) ^ ((n + 1) + (n + 1)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - Δ / 2)) ≤
      (E.card : ℝ) * (c * (β * (1 / 2 : ℝ) ^ n * δ) ^ 2) →
    η ≤ ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ X N W‖ := by
  intro F W hcut hsupp hsmall hlower hupper hscale
  have hpositive := primeHalfTests_statistic_lower P hP S favorable (ν 0) (Fin.tail ν) w
    (fun i q => hν i.succ q) hw E B β δ c hβ hδ hc hmass hbalance hendpoint hmean
    ψ X hX hψ hcE
  simp only [Fin.cons_self_tail] at hpositive
  have hW (x : Fin ((n + 1) + (n + 1)) → P) : ‖W x‖ ≤ 1 := by
    have hh (y : Fin (n + 1) → P) : ‖(w (Fin.tail y) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (hw _)]
      exact hw1 _
    change ‖(w (Fin.tail (fun i => x (i.castAdd (n + 1)))) : ℂ) *
      (w (Fin.tail (fun i => x (i.natAdd (n + 1)))) : ℂ)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (hh _) (hh _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact regularInitialAmplitude_lower_of_energy P hP (Fin.append ν ν) (Fin.append C C)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left] using hν j q)
      (fun j => by simpa only [Fin.append_right] using hν j q) i)
    (fun i => Fin.addCases (fun j => by simpa only [Fin.append_left] using hC j)
      (fun j => by simpa only [Fin.append_right] using hC j) i)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left] using hbound j q)
      (fun j => by simpa only [Fin.append_right] using hbound j q) i)
    (Fin.append F F)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, F] using (primeHalfTests_sum (n := n) P S favorable j q))
      (fun j => by simpa only [Fin.append_right, F] using (primeHalfTests_sum (n := n) P S favorable j q)) i)
    (fun i q => Fin.addCases (fun j => by simpa only [Fin.append_left, F] using (primeHalfTests_energy (n := n) P S favorable j q))
      (fun j => by simpa only [Fin.append_right, F] using (primeHalfTests_energy (n := n) P S favorable j q)) i)
    ψ X H R Δ η hX hR N W hW hcut hsupp hsmall hlower hupper (hscale.trans hpositive)

end Ostmann

end OAI
