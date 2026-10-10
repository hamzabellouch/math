import OAI.Probability.SignedSweeps.MarkedWords

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]

def coefficientProduct (f k : G → ℂ) (g : G) : ℂ := ∑ h : G, f h * k (h⁻¹ * g)

def coefficientStar (f : G → ℂ) (g : G) : ℂ := star (f g⁻¹)

def coefficientOne (g : G) : ℂ := if g = 1 then 1 else 0

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators ComplexOrder Classical
open Module
variable {G : Type*} [Group G] [Fintype G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_mul (ρ : Representation ℂ G E) (f k : G → ℂ) :
    coefficientAction ρ (coefficientProduct f k) = coefficientAction ρ f * coefficientAction ρ k := by
  simp only [coefficientAction, coefficientProduct, Finset.sum_smul]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.mul_sum]
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g => (f h * k (h⁻¹*g)) • ρ g)
  change (∑ g, (f h * k (h⁻¹*(h*g))) • ρ (h*g)) = _ at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  rw [inv_mul_cancel_left, map_mul]
  exact (smul_mul_smul_comm (f h) (ρ h) (k g) (ρ g)).symm

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_one (ρ : Representation ℂ G E) :
    coefficientAction ρ (coefficientOne (G:=G)) = 1 := by
  simp [coefficientAction, coefficientOne]

omit [FiniteDimensional ℂ E] in
lemma coefficientAction_commute (ρ : Representation ℂ G E) (P : E →ₗ[ℂ] E)
    (hP : ∀ g, ρ g * P = P * ρ g) (f : G → ℂ) :
    coefficientAction ρ f * P = P * coefficientAction ρ f := by
  simp only [coefficientAction, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hP]

lemma coefficientAction_star (ρ : Representation ℂ G E)
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ) :
    coefficientAction ρ (coefficientStar f) = (coefficientAction ρ f).adjoint := by
  simp only [coefficientAction, coefficientStar, ← LinearMap.star_eq_adjoint, star_sum, star_smul]
  rw [← Equiv.sum_comp (Equiv.inv G) (fun g => star (f g⁻¹) • ρ g)]
  simp only [Equiv.inv_apply, inv_inv]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact (unitary_representation_adjoint ρ hρ g).symm

theorem trace_product_specht_expansion {n : ℕ} (ρ : Representation ℂ (SymmetricGroup n) E)
    (f k : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f * coefficientAction ρ k) =
      ∑ lam : Partition n,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
          LinearMap.trace ℂ (Specht lam)
            (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k) := by
  simp_rw [← coefficientAction_mul]
  exact trace_specht_expansion ρ _

lemma specht_positive_coefficient_product {n : ℕ}
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive)
    (mu : Partition n) :
    0 ≤ (LinearMap.trace ℂ (Specht mu)
      (coefficientAction (spechtRepresentation mu) f * coefficientAction (spechtRepresentation mu) k)).re := by
  let := specht_irreducible mu
  exact positive_trace_product_nonneg _ _
    (coefficientAction_positive _ (spechtRepresentation_norm mu) f hf)
    (coefficientAction_positive _ (spechtRepresentation_norm mu) k hk)

lemma multiplicity_term_le_sum {I : Type*} [Fintype I] (m : I → ℕ) (a : I → ℂ)
    (ha : ∀ i, 0 ≤ (a i).re) (i : I) (c : ℕ) (hc : c ≤ m i) :
    (c : ℝ) * (a i).re ≤ (∑ j, (m j : ℂ) * a j).re := by
  rw [Complex.re_sum]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (ha i)).trans
  exact Finset.single_le_sum (fun j _ => mul_nonneg (Nat.cast_nonneg _) (ha j)) (Finset.mem_univ i)

theorem multiplicity_positive_product_trace {n : ℕ} (ρ : Representation ℂ (SymmetricGroup n) E)
    (f k : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (hk : (coefficientAction finiteRegularRepresentation k).IsPositive)
    (lam : Partition n) (c : ℕ)
    (hc : c ≤ finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ)) :
    (c : ℝ) * (LinearMap.trace ℂ (Specht lam)
      (coefficientAction (spechtRepresentation lam) f * coefficientAction (spechtRepresentation lam) k)).re ≤
        (LinearMap.trace ℂ E (coefficientAction ρ f * coefficientAction ρ k)).re := by
  calc
    _ ≤ _ := multiplicity_term_le_sum
      (fun mu => finrank ℂ (Representation.IntertwiningMap (spechtRepresentation mu) ρ))
      (fun mu => LinearMap.trace ℂ (Specht mu)
        (coefficientAction (spechtRepresentation mu) f * coefficientAction (spechtRepresentation mu) k))
      (specht_positive_coefficient_product f k hf hk) lam c hc
    _ = _ := congrArg Complex.re (trace_product_specht_expansion ρ f k).symm

end SignedSweeps
end

end OAI
