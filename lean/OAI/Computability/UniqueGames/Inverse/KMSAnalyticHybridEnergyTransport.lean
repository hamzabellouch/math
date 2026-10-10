import OAI.Computability.UniqueGames.Analysis.HybridCompositionLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas

namespace OAI

section

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']

private theorem mem_map_equiv_iff (a : E ≃ₗ[F2] E')
    (A : Submodule F2 E) (x : E) :
    a x ∈ A.map a.toLinearMap ↔ x ∈ A := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Submodule.mem_map.mp h
    exact (a.injective heq) ▸ hy
  · intro h
    exact Submodule.mem_map.mpr ⟨x, h, rfl⟩

/-- The two clauses of the actual Hybrid selector are coordinate invariant. -/
theorem hybrid_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (S : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F) :
    LinearIdentities.Hybrid (LinearEquiv.arrowCongr b a S)
      (A.map a.toLinearMap) (B.map b.toLinearMap) ↔
      LinearIdentities.Hybrid S A B := by
  constructor
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy⟩ := hr ((mem_map_equiv_iff a A x).mpr hx)
      refine ⟨b.symm y, a.injective hy⟩
    · intro y hy
      apply (mem_map_equiv_iff b B y).mp
      apply hk
      change (LinearEquiv.arrowCongr b a S) (b y) ∈ A.map a.toLinearMap
      simpa only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
        using (mem_map_equiv_iff a A (S y)).mpr hy
  · rintro ⟨hr, hk⟩
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨z, hz⟩ := hr hy
      refine ⟨b z, ?_⟩
      change a (S (b.symm (b z))) = a y
      rw [b.symm_apply_apply]
      exact congrArg a hz
    · intro y hy
      have hy' : S (b.symm y) ∈ A := (mem_map_equiv_iff a A _).mp hy
      have hm := (mem_map_equiv_iff b B _).mpr (hk hy')
      simpa only [LinearEquiv.apply_symm_apply] using hm

/-- The actual vanishing and range constraints of an affine perturbation
transport to the mapped subspaces. -/
theorem restriction_admissible_arrowCongr
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (A : Submodule F2 E) (B : Submodule F2 F) :
    (A.map a.toLinearMap ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ B.map b.toLinearMap) ↔
      (A ≤ M.ker ∧ M.range ≤ B) := by
  constructor
  · rintro ⟨hk, hr⟩
    constructor
    · intro x hx
      have heq := hk ((mem_map_equiv_iff a A x).mpr hx)
      have heq' : b (M x) = b 0 := by
        simpa only [LinearMap.mem_ker, LinearEquiv.arrowCongr_apply,
          LinearEquiv.symm_apply_apply, map_zero] using heq
      exact b.injective heq'
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff b B _).mp
      apply hr
      exact ⟨a x, by simp only [LinearEquiv.arrowCongr_apply,
        LinearEquiv.symm_apply_apply]⟩
  · rintro ⟨hk, hr⟩
    constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      change b (M (a.symm (a y))) = 0
      rw [a.symm_apply_apply, hk hy, map_zero]
    · rintro y ⟨x, rfl⟩
      apply (mem_map_equiv_iff b B _).mpr
      exact hr ⟨a.symm x, rfl⟩

/-- Transported quotient parameters give exactly the directly transported
affine perturbations; no multiplicity or normalization factor occurs. -/
theorem hybrid_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (A : Submodule F2 E) (B : Submodule F2 F) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B)).range =
      (embedding (A.map a.toLinearMap) (B.map b.toLinearMap)).range := by
  let e : (E →ₗ[F2] F) ≃ₗ[F2] (E' →ₗ[F2] F') := LinearEquiv.arrowCongr a b
  ext M'
  change (∃ N, e (embed A B N) = M') ↔
    (∃ N, embed (A.map a.toLinearMap) (B.map b.toLinearMap) N = M')
  constructor
  · rintro ⟨N, rfl⟩
    apply (exists_embed_iff _ _ _).mpr
    apply (restriction_admissible_arrowCongr a b (embed A B N) A B).mpr
    exact (exists_embed_iff A B _).mp ⟨N, rfl⟩
  · intro hM'
    let M := e.symm M'
    have he : e M = M' := e.apply_symm_apply M'
    have hm' := (exists_embed_iff _ _ _).mp hM'
    have hm : A ≤ M.ker ∧ M.range ≤ B := by
      apply (restriction_admissible_arrowCongr a b M A B).mp
      change A.map a.toLinearMap ≤ (e M).ker ∧
        (e M).range ≤ B.map b.toLinearMap
      rw [he]
      exact hm'
    obtain ⟨N, hN⟩ := (exists_embed_iff A B M).mpr hm
    exact ⟨N, by rw [hN]; exact he⟩

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

/-- The actual Fourier Hybrid projector commutes with coordinate pullback. -/
theorem hybridProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F) :
    hybridProjector A B (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [hybridProjector, linearCoeff_spectralProjector,
    NaturalTransport.linearCoeff_pullback, hybrid_arrowCongr]

/-- The actual pure-rank Fourier component commutes with coordinate pullback. -/
theorem rankComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ) :
    rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankComponent i f (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankComponent, coeff_component,
    NaturalTransport.linearCoeff_pullback, NaturalTransport.rank_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

/-- Exact normalized energy transport, with the actual Hybrid selector,
quotient restriction, and affine translate transported together. -/
theorem hybridDerivative_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) f N ^ 2 := by
  simp only [hybridDerivative, restrict, Fourier.MatrixRestrictions.translate,
    hybridProjector_pullback, map_add]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B))
    (embedding (A.map a.toLinearMap) (B.map b.toLinearMap))
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective A B))
    (embed_injective _ _) (hybrid_embedding_range a b A B)
    (fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
      (LinearEquiv.arrowCongr a b T + M) ^ 2)

/-- Pure-rank derivative energy is invariant under both coordinate changes. -/
theorem hybridDerivative_rankComponent_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M))) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) (rankComponent i f) N ^ 2 := by
  rw [rankComponent_pullback]
  exact hybridDerivative_energy_pullback a b (rankComponent i f) A B T

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
