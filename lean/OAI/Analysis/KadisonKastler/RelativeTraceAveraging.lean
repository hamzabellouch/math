import OAI.Analysis.KadisonKastler.FiniteCenter
import OAI.Analysis.KadisonKastler.TraceHullTrace

namespace OAI

/-! # Relative scalar averaging in the trace Hilbert space

The least-vector argument applies to the unitary group of an irreducible
subalgebra. This supplies the relative averaging needed for bounded-ball
tests without an amenability hypothesis on the ambient factor.
-/

namespace KadisonKastler

open Set

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}
  {τ : FaithfulTracialState (Algebra M)}

/-- The orbit under the unitary group of the given subalgebra map. -/
def relativeUnitaryOrbit (φ : R →⋆ₐ[ℂ] Algebra M) (a : Algebra M) : Set (Algebra M) :=
  Set.range fun u : unitary R => φ u * a * star (φ u)

/-- Irreducibility makes the unique least vector of a relative unitary
orbit scalar. The closure is taken in the actual trace Hilbert space. -/
theorem exists_relative_scalar_in_traceOrbit
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) :
    ∃ c : ℂ, J (c • (1 : Algebra M)) ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a) := by
  let U (u : unitary R) : unitary (Algebra M) :=
    Unitary.map (StarMonoidHom.ofClass φ) u
  have hU (u : unitary R) : (U u : Algebra M) = φ u := rfl
  have horbit : ∀ x ∈ relativeUnitaryOrbit φ a, ‖x‖ ≤ ‖a‖ := by
    rintro _ ⟨u, rfl⟩
    change ‖(U u : Algebra M) * a * star (U u : Algebra M)‖ ≤ ‖a‖
    simpa only [CStarRing.norm_coe_unitary_mul, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary] using (le_rfl : ‖a‖ ≤ ‖a‖)
  have hne : (relativeUnitaryOrbit φ a).Nonempty := by
    refine ⟨a, 1, ?_⟩
    simp
  obtain ⟨z, hz, _⟩ := exists_unique_least_norm
    (show (diagonalTraceHull J (relativeUnitaryOrbit φ a)).Nonempty from by
      obtain ⟨x, hx⟩ := hne
      exact ⟨J x, subset_closure ⟨x, subset_convexHull ℝ _ hx, rfl⟩⟩)
    isClosed_closure (diagonalTraceHull_convex J _)
  obtain ⟨b, hbz, _⟩ := traceHull_mem_ball J hJ hτ 0 (norm_nonneg a)
    (fun x hx => by simpa only [sub_zero] using horbit x hx) hz.1
  have hb : J b ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a) := hbz.symm ▸ hz.1
  have hbm : ∀ w ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a), ‖J b‖ ≤ ‖w‖ :=
    hbz.symm ▸ hz.2
  have hfix (u : unitary R) : b = (U u : Algebra M) * b * star (U u : Algebra M) := by
    apply diagonal_least_covariance J hJ (U u) (U u)
      (s := relativeUnitaryOrbit φ a) (t := relativeUnitaryOrbit φ a)
      ?_ ?_ hb hb hbm hbm
    · rintro _ ⟨v, rfl⟩
      refine ⟨u * v, ?_⟩
      simp only [hU, Submonoid.coe_mul, map_mul, star_mul, mul_assoc]
    · rintro _ ⟨v, rfl⟩
      refine ⟨star u * v, ?_⟩
      simp only [hU, Submonoid.coe_mul,
        Unitary.coe_star, map_mul, map_star, star_mul, star_star, mul_assoc]
  have hcomm (u : unitary R) : φ u * b = b * φ u := by
    have he := congrArg (fun x : Algebra M => x * (U u : Algebra M)) (hfix u)
    have he' : (U u : Algebra M) * b = b * (U u : Algebra M) := by
      simpa only [mul_assoc, Unitary.star_mul_self_of_mem (U u).property, mul_one] using he.symm
    simpa only [hU] using he'
  let T : R →ₗ[ℂ] Algebra M :=
    (LinearMap.mulRight ℂ b - LinearMap.mulLeft ℂ b).comp φ.toLinearMap
  have hcentral (r : R) : φ r * b = b * φ r := by
    have hn := norm_le_twice_unitary_bound T (C := 0) (fun u => by
      change ‖φ u * b - b * φ u‖ ≤ 0
      rw [hcomm, sub_self, norm_zero]) r
    have hz : T r = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hn) (norm_nonneg _))
    exact sub_eq_zero.mp hz
  obtain ⟨c, rfl⟩ := hirr b hcentral
  exact ⟨c, hb⟩

/-- Relative unitary conjugation preserves the given trace. -/
theorem trace_relativeUnitaryOrbit (φ : R →⋆ₐ[ℂ] Algebra M) (a : Algebra M)
    {x : Algebra M} (hx : x ∈ relativeUnitaryOrbit φ a) :
    τ.toLinearMap x = τ.toLinearMap a := by
  obtain ⟨u, rfl⟩ := hx
  have hu : star (φ u) * φ u = 1 := by
    simpa only [map_mul, map_star, map_one] using
      congrArg φ (Unitary.star_mul_self_of_mem u.property)
  calc
    _ = τ.toLinearMap (φ u * (a * star (φ u))) := congrArg τ.toLinearMap (mul_assoc _ _ _)
    _ = τ.toLinearMap ((a * star (φ u)) * φ u) := τ.tracial _ _
    _ = _ := by rw [mul_assoc, hu, mul_one]

/-- The scalar in the relative orbit hull is precisely the trace. -/
theorem trace_scalar_mem_relativeOrbit_hull
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M)) (a : Algebra M) :
    J (τ.toLinearMap a • (1 : Algebra M)) ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a) := by
  obtain ⟨c, hc⟩ := exists_relative_scalar_in_traceOrbit J hJ hτ φ hirr a
  have htrace := trace_eq_of_mem_traceHull J hJ
    (fun x hx => trace_relativeUnitaryOrbit φ a hx) hc
  simp only [map_smul, τ.map_one, smul_eq_mul, mul_one] at htrace
  rwa [htrace] at hc

end

end KadisonKastler

end OAI
