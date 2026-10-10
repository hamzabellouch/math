import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridCoefficientBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedFullGridCommonModulusLog {A : Type*} [Semiring A]
    (m : ℕ) (D P O : A) : A := 2 * (m + 1 : ℕ) * P + P ^ 2 + D * O

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type*} [Fintype X] (modulus : ℕ) [NeZero modulus] (stride : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus stride)]
variable (W : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (period : ℕ) [NeZero period]

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

omit [NeZero (residueRefinedPeriod modulus stride)] in
theorem allocatedFullGridCommonModulus_pre_bound
    {T C H : gridAxes → ℝ} {L : ℝ≥0} {D P O : ℝ} {M : ℕ}
    (he : ∀ r a, ((W r).expansion a).Bounds (T a) (Real.exp O) (C a) L (H a))
    (hP : 0 ≤ P) (hO : 0 ≤ O)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hMP : (M : ℝ) ≤ Real.exp P) (hmodulus : modulus ≤ M ^ (m + 1))
    (hperiod : period ≤ M ^ (m + 1))
    (hq : ∀ x, 0 < stride x) (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp P) :
    ∀ r (k : ∀ a, ((W r).expansion a).Term),
      0 < siteTwistCommonModulus modulus stride (W r).expansion k period ∧
      (siteTwistCommonModulus modulus stride (W r).expansion k period : ℝ) ≤
        Real.exp (allocatedFullGridCommonModulusLog m D P O) := by
  have hgrid : (Fintype.card gridAxes : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  have hpow : (M : ℝ) ^ (m + 1) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hMP (m + 1)
  have hs : (modulus : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    exact (by exact_mod_cast hmodulus : (modulus : ℝ) ≤ (M : ℝ) ^ (m + 1)).trans hpow
  have hi : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * P) := by
    exact (by exact_mod_cast hperiod : (period : ℝ) ≤ (M : ℝ) ^ (m + 1)).trans hpow
  intro r k
  refine ⟨siteTwistCommonModulus_pos modulus stride (W r).expansion k period
    (Nat.pos_of_ne_zero (NeZero.ne modulus)) hq (fun a => (he r a).period_pos (k a))
    (Nat.pos_of_ne_zero (NeZero.ne period)), ?_⟩
  apply (siteTwistCommonModulus_exp_bound modulus stride (W r).expansion k period
    hs hstride (fun a => (he r a).period_le (k a)) hi).trans
  apply Real.exp_le_exp.mpr
  have hx := mul_le_mul_of_nonneg_right hX hP
  have ha := mul_le_mul_of_nonneg_right hgrid hO
  dsimp only [allocatedFullGridCommonModulusLog]
  nlinarith only [hx, ha]

end Erdos3.VectorPolynomial

end

end OAI
