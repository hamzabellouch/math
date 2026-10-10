import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.CoefficientSubspaceEquiv

namespace OAI

namespace SiegelZeros

section
open scoped BigOperators DirectSum
namespace WeightedTorusJets.Geometry

@[instance_reducible]
noncomputable def gradedIdealQuotient
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝓐 : ℕ → Submodule K A) [GradedAlgebra 𝓐]
    (I : Ideal A) (hI : I.IsHomogeneous 𝓐) :
    GradedAlgebra (fun n => (𝓐 n).map (Ideal.Quotient.mkₐ K I).toLinearMap) where
  __ := gradedQuotientDecomposition 𝓐 (I.restrictScalars K) hI
  one_mem := ⟨1, SetLike.GradedOne.one_mem, by simp⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨x * y, SetLike.GradedMul.mul_mem hx hy, by simp⟩

end WeightedTorusJets.Geometry

end


namespace WeightedTorusJets.Geometry

theorem finrank_homogeneousSubmodule_fin (K : Type*) [Field K] (r n : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin r) K n) =
      (r + n - 1).choose n := by
  simpa using finrank_homogeneousSubmodule (σ := Fin r) (K := K) n





open MvPolynomial

theorem linear_quotient_map_homogeneous_mem
    {K σ τ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial τ K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l)
    {d : ℕ} {p : MvPolynomial τ K} (hp : p.IsHomogeneous d) :
    g p ∈ (homogeneousSubmodule σ K d).map (Ideal.Quotient.mkₐ K I).toLinearMap := by
  classical
  choose l hl hgl using hlin
  have hg : g = (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval l) := by
    ext i
    simpa only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hgl i
  refine ⟨MvPolynomial.aeval l p, ?_, ?_⟩
  · change (MvPolynomial.aeval l p).IsHomogeneous d
    simpa only [one_mul] using hp.aeval l hl
  · rw [hg]
    rfl

theorem linear_quotient_map_gradedSMul
    {K σ τ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (g : MvPolynomial τ K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    SetLike.GradedSMul (homogeneousSubmodule τ K)
      (fun n => (homogeneousSubmodule σ K n).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let _ := g.toRingHom.toAlgebra
  let _ : Module (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toModule
  let _ : SMul (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  constructor
  intro i j p y hp hy
  obtain ⟨a, ha, hga⟩ := linear_quotient_map_homogeneous_mem I g hlin hp
  obtain ⟨b, hb, hgb⟩ := hy
  refine ⟨a * b, ?_, ?_⟩
  · exact SetLike.GradedMul.mul_mem ha hb
  · change Ideal.Quotient.mk I (a * b) = g p * y
    rw [map_mul]
    exact congrArg₂ (· * ·) hga hgb

end WeightedTorusJets.Geometry



namespace WeightedTorusJets

theorem normalization_quotient_finite_torsionFree_finiteVariables {K σ : Type*} [Field K] [Finite σ] {s : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (g : MvPolynomial (Fin s) K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hg : Function.Injective g) (hint : g.toRingHom.IsIntegral) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    IsScalarTower K (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) ∧
      Module.Finite (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) ∧
      Module.IsTorsionFree (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) := by
  let _ := g.toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toModule
  let _ : SMul (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  let : IsScalarTower K (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    IsScalarTower.of_algHom g
  let : Algebra.FiniteType K (MvPolynomial σ K ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective
  let : Algebra.FiniteType (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin s) K)
      (MvPolynomial σ K ⧸ I)
  let : Algebra.IsIntegral (MvPolynomial (Fin s) K) (MvPolynomial σ K ⧸ I) :=
    ⟨hint⟩
  exact ⟨inferInstance, Algebra.IsIntegral.finite,
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg⟩

end WeightedTorusJets


namespace WeightedTorusJets.Geometry.GradedQuotient

open MvPolynomial Filter

attribute [local instance] MvPolynomial.gradedAlgebra

theorem hilbertPolynomial_normalization_finiteVariables
    {K σ : Type*} [Field K] [Finite σ] {d : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (g : MvPolynomial (Fin (d + 1)) K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hg : Function.Injective g) (hint : g.toRingHom.IsIntegral)
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    (hilbertPolynomial I hI).natDegree = d ∧ projectiveDegree I hI =
      Module.finrank (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) := by
  let _ := g.toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toModule
  let _ : SMul (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
    g.toRingHom.toAlgebra.toSMul
  obtain ⟨htower, hfinite, htfree⟩ :=
    WeightedTorusJets.normalization_quotient_finite_torsionFree_finiteVariables I g hg hint
  let 𝓐 := homogeneousSubmodule (Fin (d + 1)) K
  let 𝓜 := degreePiece I
  have : GradedAlgebra 𝓜 := gradedIdealQuotient (homogeneousSubmodule σ K) I hI
  have : SetLike.GradedSMul 𝓐 𝓜 := linear_quotient_map_gradedSMul I g hlin
  have : ∀ m, Module.Finite K (𝓜 m) := by
    intro m
    have : Module.Finite K (homogeneousSubmodule σ K m) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg σ K m)
    exact Module.Finite.map _ _
  have hdim (m : ℕ) : Module.finrank K (𝓐 m) = (m + d).choose d := by
    rw [finrank_homogeneousSubmodule_fin]
    have hm : d + 1 + m - 1 = m + d := by omega
    rw [hm, Nat.choose_symm_add]
  have hP : ∀ᶠ m : ℕ in atTop,
      (Module.finrank K (𝓜 m) : ℚ) = (hilbertPolynomial I hI).eval (m : ℚ) := by
    obtain ⟨N, hN⟩ := hilbertPolynomial_spec I hI
    filter_upwards [eventually_gt_atTop N] with m hm
    exact hN m hm
  have h := hilbertPolynomial_degree_coefficient_eq_rank 𝓐 𝓜
    (a := X (0 : Fin (d + 1))) (X_ne_zero _) (isHomogeneous_X K _) d hdim
    (hilbertPolynomial I hI) hP
  have heq : (projectiveDegree I hI : ℚ) =
      (Module.finrank (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) : ℚ) := by
    rw [projectiveDegree_cast, h.1]
    exact h.2
  exact ⟨h.1, by exact_mod_cast heq⟩

theorem projectiveDegree_eq_normalization_rank_finiteVariables
    {K σ : Type*} [Field K] [Finite σ] {d : ℕ}
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (g : MvPolynomial (Fin (d + 1)) K →ₐ[K] (MvPolynomial σ K ⧸ I))
    (hg : Function.Injective g) (hint : g.toRingHom.IsIntegral)
    (hlin : ∀ i, ∃ l : MvPolynomial σ K,
      l.IsHomogeneous 1 ∧ g (X i) = Ideal.Quotient.mk I l) :
    let _ := g.toRingHom.toAlgebra
    let _ : Module (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toModule
    let _ : SMul (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
      g.toRingHom.toAlgebra.toSMul
    projectiveDegree I hI =
      Module.finrank (MvPolynomial (Fin (d + 1)) K) (MvPolynomial σ K ⧸ I) :=
  (hilbertPolynomial_normalization_finiteVariables I hI g hg hint hlin).2

end WeightedTorusJets.Geometry.GradedQuotient



end SiegelZeros

end OAI
