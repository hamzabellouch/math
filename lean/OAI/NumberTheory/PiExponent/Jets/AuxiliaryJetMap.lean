import OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

noncomputable def literalJetSubstitution {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C (1 + Polynomial.X))
    (fun i => MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) + MvPolynomial.X i))

noncomputable def literalJetEvaluation {m : ℕ} (K : ℕ)
    (V : Fin (m + 1) → ℝ) (H : ℝ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) :
    PiExponentApprox.FramePolynomial m →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ => (Polynomial.lcoeff ℂ (ρ.2.val 0)).comp
    (((MvPolynomial.lcoeff (Polynomial ℂ)
      (InterpolationMatrix.exponentVector (fun i => ρ.2.val i.succ))).restrictScalars ℂ).comp
        (literalJetSubstitution r G ρ.1.val).toLinearMap))

@[simp] theorem literalJetEvaluation_apply {m : ℕ} (K : ℕ)
    (V : Fin (m + 1) → ℝ) (H : ℝ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (p : PiExponentApprox.FramePolynomial m)
    (ρ : Fin K × ↥(strictWeightedSimplex V H)) :
    literalJetEvaluation K V H r G p ρ =
      ((literalJetSubstitution r G ρ.1.val p).coeff
        (InterpolationMatrix.exponentVector (fun i => ρ.2.val i.succ))).coeff (ρ.2.val 0) := rfl

theorem literalJetSubstitution_monomial {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) (e : Fin (m + 1) → ℕ) (z : ℂ) :
    literalJetSubstitution r G j
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z) =
      MvPolynomial.C (Polynomial.C z) *
        InterpolationMatrix.monomialImage r G j (e 0) (fun i => e i.succ) := by
  classical
  rw [literalJetSubstitution, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp only [InterpolationMatrix.exponentVector_apply, Fin.cases_zero, Fin.cases_succ,
    InterpolationMatrix.monomialImage, ← map_pow]
  rfl

theorem literalJetSubstitution_polynomialOfCoefficients {m : ℕ}
    (S : Finset (Fin (m + 1) → ℕ)) (x : S → ℂ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (j : ℕ) :
    literalJetSubstitution r G j (polynomialOfCoefficients S x) =
      InterpolationMatrix.sectionImage r G (fun c : S => c.val 0)
        (fun c i => c.val i.succ) x j := by
  classical
  change literalJetSubstitution r G j
    (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)) = _
  simp only [map_sum, literalJetSubstitution_monomial, InterpolationMatrix.sectionImage]

theorem eventually_exists_literalJet_auxiliaryPolynomial {m : ℕ}
    (W V : Fin (m + 1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ ρ : Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)),
        ((literalJetSubstitution r G ρ.1.val p).coeff
          (InterpolationMatrix.exponentVector (fun i => ρ.2.val i.succ))).coeff (ρ.2.val 0) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨p, hp, hw, he⟩ := hN (literalJetEvaluation K (fun i => (V i : ℝ)) (a * N) r G)
  refine ⟨p, hp, hw, ?_⟩
  intro ρ
  have h := congrFun he ρ
  simpa only [literalJetEvaluation_apply, Pi.zero_apply] using h

end PiExponent

end OAI
