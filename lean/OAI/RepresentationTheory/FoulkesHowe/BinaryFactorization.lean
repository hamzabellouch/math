import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- Binary forms used in the first step of the vanishing argument split into linear factors. -/
theorem binary_power_factorization {A : Type*} [CommRing A] [Algebra ℂ A]
    (r : ℕ) (hr : 0 < r) (x y : A) (c : ℂ) :
    ∃ z : Fin r → ℂ, (∏ i : Fin r, (x - z i • y)) = x ^ r + c • y ^ r := by
  classical
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-c) hr
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / r)
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hr.ne'
  have hp : (Polynomial.X ^ r - Polynomial.C (-c) : Polynomial ℂ) =
      ∏ i ∈ Finset.range r, (Polynomial.X - Polynomial.C (ζ ^ i * α)) :=
    X_pow_sub_C_eq_prod hζ hr hα
  have hh := congrArg (fun p : Polynomial ℂ => p.homogenize r) hp
  have hd : ∀ i ∈ Finset.range r,
      (Polynomial.X - Polynomial.C (ζ ^ i * α)).natDegree ≤ 1 := by
    intro i hi
    rw [Polynomial.natDegree_X_sub_C]
  have hprod := Polynomial.homogenize_finsetProd (n := fun _ : ℕ => 1) hd
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hprod
  rw [hprod] at hh
  simp only [Polynomial.homogenize_sub, Polynomial.homogenize_X_pow le_rfl,
    Nat.sub_self, pow_zero, mul_one, Polynomial.homogenize_C,
    Polynomial.homogenize_X (by decide : (1 : ℕ) ≠ 0), Nat.sub_self, pow_one] at hh
  have he := congrArg (MvPolynomial.aeval ![x, y]) hh
  simp only [map_sub, map_pow, map_mul, map_prod, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    MvPolynomial.aeval_C] at he
  refine ⟨fun i => ζ ^ (i : ℕ) * α, ?_⟩
  change (∏ i : Fin r, (x - (ζ ^ (i : ℕ) * α) • y)) = _
  rw [Fin.prod_univ_eq_prod_range (fun i => x - (ζ ^ i * α) • y)]
  simpa only [Algebra.smul_def, map_neg, neg_mul, sub_neg_eq_add, map_mul, map_pow] using he.symm

/-- In the symmetric algebra, a binary sum of pure powers is a product of vectors. -/
theorem symMonomialRaw_binary_power (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r : ℕ) (hr : 0 < r) (x y : V) (c : ℂ) :
    ∃ v : Fin r → V, symMonomialRaw r V v =
      (SymmetricAlgebra.ι ℂ V x) ^ r + c • (SymmetricAlgebra.ι ℂ V y) ^ r := by
  obtain ⟨z, hz⟩ := binary_power_factorization r hr
    (SymmetricAlgebra.ι ℂ V x) (SymmetricAlgebra.ι ℂ V y) c
  refine ⟨fun i => x - z i • y, ?_⟩
  simpa only [symMonomialRaw, map_sub, map_smul] using hz

/-- Multiplying a split binary power by a product remains a product, with the exact degree. -/
theorem symMonomialRaw_binary_power_mul (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r m : ℕ) (hr : 0 < r) (x y : V) (c : ℂ) (u : Fin m → V) :
    ∃ v : Fin (r + m) → V, symMonomialRaw (r + m) V v =
      ((SymmetricAlgebra.ι ℂ V x) ^ r + c • (SymmetricAlgebra.ι ℂ V y) ^ r) *
        symMonomialRaw m V u := by
  obtain ⟨w, hw⟩ := symMonomialRaw_binary_power V r hr x y c
  refine ⟨Fin.append w u, ?_⟩
  rw [← hw]
  simp only [symMonomialRaw, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- The split binary form is a genuine product in the prescribed symmetric-power subtype. -/
theorem symMonomial_binary_power_mul (V : Type*) [AddCommGroup V] [Module ℂ V]
    (r m : ℕ) (hr : 0 < r) (x y : V) (c : ℂ) (u : Fin m → V) :
    ∃ v : Fin (r + m) → V, symMonomial (r + m) V v =
      symMonomial (r + m) V (Fin.append (fun _ : Fin r => x) u) +
        c • symMonomial (r + m) V (Fin.append (fun _ : Fin r => y) u) := by
  obtain ⟨v, hv⟩ := symMonomialRaw_binary_power_mul V r m hr x y c u
  refine ⟨v, Subtype.ext ?_⟩
  change symMonomialRaw (r + m) V v = _
  rw [hv]
  simp only [symMonomial, Submodule.coe_add, Submodule.coe_smul, symMonomialRaw,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, add_mul, smul_mul_assoc]

end Problem346

end

end OAI
