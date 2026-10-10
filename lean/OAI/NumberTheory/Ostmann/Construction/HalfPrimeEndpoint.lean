import OAI.NumberTheory.Ostmann.Construction.HalfPrimeFactorization

namespace OAI

/-! # The common endpoint scalar in the Section 7 half-list -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def endpointResidueValue {p : ℕ} (S : Finset (ZMod p)) : ℝ :=
  (1 - residueDensity S) / Real.sqrt (residueVariance S)

theorem normalizedResidueIndicator_endpoint {p : ℕ} (S : Finset (ZMod p))
    (a : ZMod p) (ha : a ∈ S) :
    normalizedResidueIndicator S a = (endpointResidueValue S : ℂ) := by
  simp only [normalizedResidueIndicator, endpointResidueValue, centeredDensity,
    ite_eq_left ha, residueDensity]

theorem endpointResidueValue_nonneg {p : ℕ} [NeZero p] (S : Finset (ZMod p)) :
    0 ≤ endpointResidueValue S := by
  have hcard : S.card ≤ p := by simpa only [ZMod.card] using S.card_le_univ
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hd : residueDensity S ≤ 1 := by
    rw [residueDensity, div_le_one hp]
    exact_mod_cast hcard
  exact div_nonneg (sub_nonneg.mpr hd) (Real.sqrt_nonneg _)

/-- A fixed absolute lower bound suffices for the exponential half-list loss. -/
theorem endpointResidueValue_balanced {p : ℕ} (S : Finset (ZMod p))
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3) :
    (1 / 2 : ℝ) ≤ endpointResidueValue S := by
  have hv : 0 < residueVariance S := by
    unfold residueVariance
    nlinarith
  have hs : 0 < Real.sqrt (residueVariance S) := Real.sqrt_pos.mpr hv
  have hsq := Real.sq_sqrt hv.le
  have hbound : Real.sqrt (residueVariance S) ≤ 2 * (1 - residueDensity S) := by
    have hvar : residueVariance S ≤ (2 * (1 - residueDensity S)) ^ 2 := by
      unfold residueVariance
      nlinarith
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  rw [endpointResidueValue, le_div_iff₀ hs]
  linarith

theorem halfPrimeScalar_nonneg {n : ℕ} (P : Finset ℕ)
    (μ : Fin n → P → ℝ) (w : (Fin n → P) → ℝ) (c : Fin n → P → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hw : ∀ x, 0 ≤ w x) (hc : ∀ i p, 0 ≤ c i p) :
    0 ≤ halfPrimeScalar P μ w c :=
  Finset.sum_nonneg (fun x _ => mul_nonneg
    (mul_nonneg (productPrior_nonneg μ hμ x) (hw x))
    (Finset.prod_nonneg (fun i _ => hc i (x i))))

/-- The endpoint mean of the actual giant, and the balanced weighted event for
the nongiant slots, give the doubled original-prior physical lower bound.
The cutoffs remain inside the half-list weight. -/
theorem halfPrimeMean_giant_endpoint_lower {n : ℕ}
    (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)]
    (μ₀ : P → ℝ) (μ : Fin n → P → ℝ)
    (F₀ : (q : P) → ZMod (q : ℕ) → ℂ)
    (F : Fin n → (q : P) → ZMod (q : ℕ) → ℂ)
    (w : (Fin n → P) → ℝ) (cval : Fin n → P → ℝ)
    (hμ : ∀ i q, 0 ≤ μ i q) (hw : ∀ x, 0 ≤ w x)
    (hcval : ∀ i q, 0 ≤ cval i q)
    (hF₀ : ∀ q a, (F₀ q a).im = 0) (hF : ∀ i q a, (F i q a).im = 0)
    (E : Finset ℤ) (S : Finset (Fin n → P)) (β γ δ c : ℝ)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hmass : β ≤ ∑ x ∈ S, productPrior μ x * w x)
    (hgood : ∀ x ∈ S, ∀ i, γ ≤ cval i (x i))
    (hendpoint : ∀ a ∈ E, ∀ i q, F i q (a : ZMod (q : ℕ)) = (cval i q : ℂ))
    (hmean : (E.card : ℝ) * δ ≤
      ∑ a ∈ E, (∑ q : P, (μ₀ q : ℂ) * F₀ q (a : ZMod (q : ℕ))).re)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hcE : ∀ a ∈ E, c ≤ (ψ ((a : ℝ) / X)).re) :
    let ν := Fin.cons μ₀ μ
    let H := Fin.cons F₀ F
    let W := fun y : Fin (n + 1) → P => (w (Fin.tail y) : ℂ)
    (E.card : ℝ) * (c * (β * γ ^ n * δ) ^ 2) ≤
      ‖∑ x : Fin ((n + 1) + (n + 1)) → P,
        (productPrior (Fin.append ν ν) x : ℂ) * doubledHalfWeight W x *
          physicalTupleSum P x (Fin.append H H) ψ X‖ := by
  dsimp only
  let κ := halfPrimeScalar P μ w cval
  have hk : 0 ≤ κ := halfPrimeScalar_nonneg P μ w cval hμ hw hcval
  have hkl : β * γ ^ n ≤ κ := halfPrimeScalar_lower P μ w cval hμ hw hcval
    S β γ hγ hmass hgood
  apply halfPrimeMean_endpoint_lower P (Fin.cons μ₀ μ) (Fin.cons F₀ F)
    (fun y => (w (Fin.tail y) : ℂ)) ψ X hX
    (fun a => halfPrimeMean_real P _ _ _
      (fun i q b => Fin.cases (hF₀ q b) (fun j => hF j q b) i)
      (fun _ => Complex.ofReal_im _) a)
    E c (β * γ ^ n * δ) hc (by positivity) hψ hcE
  have heq : (∑ a ∈ E, (halfPrimeMean P (Fin.cons μ₀ μ) (Fin.cons F₀ F)
      (fun y => (w (Fin.tail y) : ℂ)) a).re) =
      κ * ∑ a ∈ E, (∑ q : P, (μ₀ q : ℂ) * F₀ q (a : ZMod (q : ℕ))).re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [halfPrimeMean_cons_scalar P μ₀ μ F₀ F w cval a (hendpoint a ha)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, κ]
  rw [heq]
  calc
    _ ≤ κ * ((E.card : ℝ) * δ) := by
      have h := mul_le_mul_of_nonneg_right hkl
        (mul_nonneg (Nat.cast_nonneg E.card) hδ)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean hk

end Ostmann

end OAI
