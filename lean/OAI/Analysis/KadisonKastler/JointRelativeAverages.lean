import OAI.Analysis.KadisonKastler.FiniteRelativeAverages
import OAI.Analysis.KadisonKastler.TracialProducts

namespace OAI

/-! # Simultaneous finite relative averages

Successively averaging two elements gives one finite family controlling
both. The second average cannot increase the first element's tracial
norm; its trace preserves the scalar target for the second element.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A R E : Type*} [CStarAlgebra A] [CStarAlgebra R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Equal-weight conjugation by a finite family from the source algebra. -/
def relativeConjugationAverage {I : Type*} [Fintype I]
    (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (a : A) : A :=
  finiteAverage (fun i => φ (u i) * a * star (φ (u i)))

private theorem trace_relativeConjugation (τ : FaithfulTracialState A)
    (φ : R →⋆ₐ[ℂ] A) (u : unitary R) (a : A) :
    τ.toLinearMap (φ u * a * star (φ u)) = τ.toLinearMap a := by
  have hu : star (φ u) * φ u = 1 := by
    simpa only [map_mul, map_star, map_one] using
      congrArg φ (Unitary.star_mul_self_of_mem u.property)
  calc
    _ = τ.toLinearMap (φ u * (a * star (φ u))) := congrArg τ.toLinearMap (mul_assoc _ _ _)
    _ = τ.toLinearMap ((a * star (φ u)) * φ u) := τ.tracial _ _
    _ = _ := by rw [mul_assoc, hu, mul_one]

/-- Every finite relative average preserves the trace. -/
theorem trace_relativeConjugationAverage {I : Type*} [Fintype I] [Nonempty I]
    (τ : FaithfulTracialState A) (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (a : A) :
    τ.toLinearMap (relativeConjugationAverage φ u a) = τ.toLinearMap a := by
  unfold relativeConjugationAverage finiteAverage
  simp only [map_smul, map_sum, trace_relativeConjugation, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp [Fintype.card_ne_zero]

/-- A finite relative average is contractive for the tracial two-norm. -/
theorem traceTwoNorm_relativeConjugationAverage_le {I : Type*}
    [Fintype I] [Nonempty I] (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (a : A) :
    traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ traceTwoNorm τ a := by
  rw [← hJ]
  have he : J (relativeConjugationAverage φ u a) =
      finiteAverage (fun i => J (φ (u i) * a * star (φ (u i)))) := by
    simp only [relativeConjugationAverage, finiteAverage, map_smul, map_sum]
  rw [he]
  apply norm_finiteAverage_le
  intro i
  rw [hJ]
  let v : unitary A := Unitary.map (StarMonoidHom.ofClass φ) (u i)
  change traceTwoNorm τ ((v : A) * a * (star v : unitary A)) ≤ traceTwoNorm τ a
  simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  exact le_rfl

/-- The Cartesian-product family implements composition of averages. -/
theorem relativeConjugationAverage_comp {I K : Type*} [Fintype I] [Fintype K]
    (φ : R →⋆ₐ[ℂ] A) (u : I → unitary R) (v : K → unitary R) (a : A) :
    relativeConjugationAverage φ (fun ki : K × I => v ki.1 * u ki.2) a =
      relativeConjugationAverage φ v (relativeConjugationAverage φ u a) := by
  have hcard : (Fintype.card (K × I) : ℂ)⁻¹ =
      (Fintype.card K : ℂ)⁻¹ * (Fintype.card I : ℂ)⁻¹ := by
    rw [Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm]
  simp only [relativeConjugationAverage, finiteAverage, hcard,
    Fintype.sum_prod_type, Submonoid.coe_mul, map_mul, star_mul,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    Finset.smul_sum, smul_smul, mul_assoc]

private theorem traceTwoNorm_scalar_one (τ : FaithfulTracialState A)
    (J : A →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (c : ℂ) :
    traceTwoNorm τ (c • (1 : A)) = ‖c‖ := by
  rw [← hJ, map_smul, norm_smul, hJ, traceTwoNorm_one, mul_one]

/-- Any scalar-averaging property supplies simultaneous two-norm bounds
for two trace-bounded elements. No positivity assumption is needed. -/
theorem exists_joint_relative_averages_of_scalar
    (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (φ : R →⋆ₐ[ℂ] A)
    (havg : ∀ a : A, ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧
      ∃ u : Fin n → unitary R,
        traceTwoNorm τ (relativeConjugationAverage φ u a -
          τ.toLinearMap a • (1 : A)) < ε)
    (a b : A) (ha : ‖τ.toLinearMap a‖ ≤ 1) (hb : ‖τ.toLinearMap b‖ ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → unitary R,
      traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ 2 ∧
      traceTwoNorm τ (relativeConjugationAverage φ u b) ≤ 2 := by
  classical
  obtain ⟨m, hm, u, hu⟩ := havg a 1 zero_lt_one
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have ha' : traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ 2 := by
    have htriangle := traceTwoNorm_add_le τ
      (relativeConjugationAverage φ u a - τ.toLinearMap a • (1 : A))
      (τ.toLinearMap a • (1 : A))
    rw [sub_add_cancel, traceTwoNorm_scalar_one τ J hJ] at htriangle
    linarith
  obtain ⟨n, hn, v, hv⟩ := havg (relativeConjugationAverage φ u b) 1 zero_lt_one
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [trace_relativeConjugationAverage] at hv
  have hb' : traceTwoNorm τ
      (relativeConjugationAverage φ v (relativeConjugationAverage φ u b)) ≤ 2 := by
    have htriangle := traceTwoNorm_add_le τ
      (relativeConjugationAverage φ v (relativeConjugationAverage φ u b) -
        τ.toLinearMap (relativeConjugationAverage φ u b) • (1 : A))
      (τ.toLinearMap (relativeConjugationAverage φ u b) • (1 : A))
    rw [sub_add_cancel, traceTwoNorm_scalar_one τ J hJ,
      trace_relativeConjugationAverage] at htriangle
    linarith
  let K := Fin n × Fin m
  let σ : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let w : K → unitary R := fun ki => v ki.1 * u ki.2
  have he (x : A) : relativeConjugationAverage φ (fun j => w (σ j)) x =
      relativeConjugationAverage φ v (relativeConjugationAverage φ u x) := by
    calc
      _ = relativeConjugationAverage φ w x := by
        unfold relativeConjugationAverage finiteAverage
        rw [Fintype.card_congr σ]
        congr 1
        exact σ.sum_comp (fun ki => φ (w ki) * x * star (φ (w ki)))
      _ = _ := relativeConjugationAverage_comp φ u v x
  refine ⟨Fintype.card K, Fintype.card_pos, fun j => w (σ j), ?_, ?_⟩
  · rw [he]
    exact (traceTwoNorm_relativeConjugationAverage_le τ J hJ φ v _).trans ha'
  · rw [he]
    exact hb'

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CompleteSpace E] {M : VonNeumannAlgebra H}

/-- In a concrete finite factor, irreducibility supplies one actual
finite family simultaneously averaging any two trace-bounded elements. -/
theorem exists_joint_finite_relative_average
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a b : Algebra M) (ha : ‖τ.toLinearMap a‖ ≤ 1) (hb : ‖τ.toLinearMap b‖ ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ u : Fin n → unitary R,
      traceTwoNorm τ (relativeConjugationAverage φ u a) ≤ 2 ∧
      traceTwoNorm τ (relativeConjugationAverage φ u b) ≤ 2 := by
  apply exists_joint_relative_averages_of_scalar τ J hJ φ ?_ a b ha hb
  intro x ε hε
  simpa only [relativeConjugationAverage, finiteAverage, Fintype.card_fin] using
    exists_finite_relative_scalar_average J hJ hτ φ hirr x hε

end

end KadisonKastler

end OAI
