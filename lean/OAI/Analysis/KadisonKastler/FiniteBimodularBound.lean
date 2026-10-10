import OAI.Analysis.KadisonKastler.JointRelativeAverages
import OAI.Analysis.KadisonKastler.BalancedOrbitFamilies
import OAI.Analysis.KadisonKastler.FiniteCovariancePairing

namespace OAI

/-! # Bounded-ball tests for bimodular operators

Relative scalar averaging supplies the finite covariance families. The
left and right unitary actions then preserve their pairings, so the
proved sign-randomization and clipping estimate applies with constant 384.
-/

namespace KadisonKastler

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}

private theorem norm_trace_square_le_one {A : Type*} [CStarAlgebra A]
    (τ : FaithfulTracialState A) (a : A) (ha : traceTwoNorm τ a ≤ 1) :
    ‖τ.toLinearMap (star a * a)‖ ≤ 1 := by
  have h := τ.cauchySchwarz a a
  nlinarith [traceTwoNorm_nonneg τ a]

private theorem norm_trace_square_reverse_le_one {A : Type*} [CStarAlgebra A]
    (τ : FaithfulTracialState A) (a : A) (ha : traceTwoNorm τ a ≤ 1) :
    ‖τ.toLinearMap (a * star a)‖ ≤ 1 := by
  rw [τ.tracial a (star a)]
  exact norm_trace_square_le_one τ a ha

/-- Irreducibility and bimodularity produce the actual finite families
required for covariance testing. -/
theorem exists_finite_bimodular_covariance_families
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (V : E →L[ℂ] E) (L Q : unitary R → unitary (E →L[ℂ] E))
    (hL : ∀ (u : unitary R) (x : Algebra M), J (φ u * x) = (L u : E →L[ℂ] E) (J x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), J (x * φ u) = (Q u : E →L[ℂ] E) (J x))
    (hVL : ∀ u, Commute V (L u : E →L[ℂ] E))
    (hVQ : ∀ u, Commute V (Q u : E →L[ℂ] E))
    (a b : Algebra M) (ha : traceTwoNorm τ a ≤ 1) (hb : traceTwoNorm τ b ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ ∃ f g : Fin n → Algebra M,
      (∀ i, traceTwoNorm τ (f i) ≤ 1) ∧
      (∀ i, traceTwoNorm τ (g i) ≤ 1) ∧
      traceTwoNorm τ (finiteSignRightCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance f) ≤ 2 ∧
      traceTwoNorm τ (finiteSignRightCovariance g) ≤ 2 ∧
      traceTwoNorm τ (finiteSignLeftCovariance g) ≤ 2 ∧
      (∀ i, inner ℂ (V (J (f i))) (J (g i)) = inner ℂ (V (J a)) (J b)) := by
  obtain ⟨m, hm, u, hua, hub⟩ := exists_joint_finite_relative_average τ J hJ hτ φ hirr
    (a * star a) (b * star b)
    (norm_trace_square_reverse_le_one τ a ha) (norm_trace_square_reverse_le_one τ b hb)
  obtain ⟨n, hn, v, hva, hvb⟩ := exists_joint_finite_relative_average τ J hJ hτ φ hirr
    (star a * a) (star b * b)
    (norm_trace_square_le_one τ a ha) (norm_trace_square_le_one τ b hb)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let d : Fin m → unitary (Algebra M) := fun i =>
    Unitary.map (StarMonoidHom.ofClass φ) (u i)
  let e : Fin n → unitary (Algebra M) := fun j =>
    star (Unitary.map (StarMonoidHom.ofClass φ) (v j))
  have hd : ∀ i x, J ((d i : Algebra M) * x) = (L (u i) : E →L[ℂ] E) (J x) := by
    intro i x
    exact hL (u i) x
  have he : ∀ j x, J (x * (e j : Algebra M)) =
      (Q (star (v j)) : E →L[ℂ] E) (J x) := by
    intro j x
    change J (x * star (φ (v j))) = (Q (star (v j)) : E →L[ℂ] E) (J x)
    simpa only [Unitary.coe_star, map_star] using hQ (star (v j)) x
  have hQa : traceTwoNorm τ (finiteAverage
      (fun j => star (e j : Algebra M) * (star a * a) * (e j : Algebra M))) ≤ 2 := by
    change traceTwoNorm τ (finiteAverage
      (fun j => star (star (φ (v j))) * (star a * a) * star (φ (v j)))) ≤ 2
    simpa only [relativeConjugationAverage, star_star] using hva
  have hQb : traceTwoNorm τ (finiteAverage
      (fun j => star (e j : Algebra M) * (star b * b) * (e j : Algebra M))) ≤ 2 := by
    change traceTwoNorm τ (finiteAverage
      (fun j => star (star (φ (v j))) * (star b * b) * star (φ (v j)))) ≤ 2
    simpa only [relativeConjugationAverage, star_star] using hvb
  exact exists_balanced_orbit_families τ J V d e
    (fun i => L (u i)) (fun j => Q (star (v j))) hd he
    (fun i => hVL (u i)) (fun j => hVQ (star (v j))) a b ha hb
    hQa hua hQb hub

/-- Unit-ball tests control a bounded bimodular operator on the trace
Hilbert realization, with the manuscript's constant 384. -/
theorem opNorm_le_of_irreducible_bimodular_tests
    (τ : FaithfulTracialState (Algebra M)) (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hJdense : DenseRange J)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (V : E →L[ℂ] E) (L Q : unitary R → unitary (E →L[ℂ] E))
    (hL : ∀ (u : unitary R) (x : Algebra M), J (φ u * x) = (L u : E →L[ℂ] E) (J x))
    (hQ : ∀ (u : unitary R) (x : Algebra M), J (x * φ u) = (Q u : E →L[ℂ] E) (J x))
    (hVL : ∀ u, Commute V (L u : E →L[ℂ] E))
    (hVQ : ∀ u, Commute V (Q u : E →L[ℂ] E)) {K : ℝ}
    (hK : ∀ x y : Algebra M, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖inner ℂ (V (J x)) (J y)‖ ≤ K) : ‖V‖ ≤ 384 * K := by
  let : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder (Algebra M)
  let : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing (Algebra M)
  apply opNorm_le_of_finite_covariance_families τ J hJ hJdense V hK
  intro a b ha hb
  exact exists_finite_bimodular_covariance_families τ J hJ hτ φ hirr
    V L Q hL hQ hVL hVQ a b ha hb

end

end KadisonKastler

end OAI
