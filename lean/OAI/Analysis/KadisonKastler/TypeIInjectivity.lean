import OAI.Analysis.KadisonKastler.TypeICyclicRepresentation
import OAI.Analysis.KadisonKastler.KaplanskyDensity

namespace OAI

/-! # Injectivity of type I factors in their given representation

The cyclic restriction at a minimal projection is faithful and irreducible.
Kaplansky approximation and weak compactness of the original operator ball
make it surjective onto all operators on that cyclic space.  Compression,
followed by the inverse restriction, is therefore an ambient contractive
projection onto the original algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem typeICyclicHom_bicommutant (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hpξ : p.val.val ξ = ξ)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) :
    T ∈ Set.centralizer (Set.centralizer
      (Set.range (typeICyclicHom (M := M) ξ))) := by
  intro S hS
  obtain ⟨z, rfl⟩ := typeICyclicHom_commutant p hp ξ hpξ S
    (fun a => hS _ ⟨a, rfl⟩)
  simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes z T

/-- Every operator on the minimal cyclic space comes from the original
factor; the assertion includes the closed unit ball without norm loss. -/
theorem typeICyclicHom_surjective_unitBall (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)
    (T : typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) (hT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ typeICyclicHom ξ a = T := by
  classical
  let K := typeICyclicSpace M ξ
  let ρ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K) := typeICyclicHom ξ
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := ρ.range
  have hcomm : T ∈ Set.centralizer (Set.centralizer (A : Set (K →L[ℂ] K))) := by
    intro S hS
    obtain ⟨z, hscalar⟩ := typeICyclicHom_commutant p hp ξ hpξ S
      (fun a => hS (ρ a) ⟨a, rfl⟩)
    change S * T = T * S
    rw [hscalar]
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes z T
  have hnet := publishedKaplanskyDensity.exists_weak_contraction_net (H := K)
    A T hcomm hT
  let c : Finset K × ℕ → A := Classical.choose hnet
  have hc : ∀ d, ‖c d‖ ≤ 1 := (Classical.choose_spec hnet).1
  have hlim : ∀ x y : K, Tendsto (fun d => inner ℂ y ((c d).val x)) atTop
      (𝓝 (inner ℂ y (T x))) := (Classical.choose_spec hnet).2
  choose a ha using fun d => (c d).property
  have ha' (d : Finset K × ℕ) : ρ (a d) = (c d).val := ha d
  have hn (d : Finset K × ℕ) : ‖a d‖ ≤ 1 := by
    rw [← typeICyclicHom_norm hM p hp ξ hξ hpξ]
    change ‖ρ (a d)‖ ≤ 1
    rw [ha' d]
    exact hc d
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun d => (a d).val) 1 zero_le_one hn
  let a₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨a₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ : Tendsto (fun d => inner ℂ y (ρ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (ρ a₀ x))) := hweak x.val y.val
  have h₂ : Tendsto (fun d => inner ℂ y (ρ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem typeICyclicHom_surjective (hM : ScalarCenter M)
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p)
    (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ) :
    Function.Surjective (typeICyclicHom (M := M) ξ) := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) := {}
  intro T
  by_cases hT : T = 0
  · exact ⟨0, by rw [map_zero, hT]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := typeICyclicHom_surjective_unitBall hM p hp ξ hξ hpξ
    ((‖T‖ : ℂ)⁻¹ • T) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  calc
    typeICyclicHom ξ ((‖T‖ : ℂ) • a) =
        (‖T‖ : ℂ) • typeICyclicHom ξ a := rfl
    _ = T := by
      rw [ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

/-- The algebraic identification with all operators on the minimal cyclic
space, constructed in the original representation. -/
def typeICyclicEquiv (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (ξ : H) (hξ : ξ ≠ 0)
    (hpξ : p.val.val ξ = ξ) :
    Algebra M ≃⋆ₐ[ℂ] (typeICyclicSpace M ξ →L[ℂ] typeICyclicSpace M ξ) :=
  StarAlgEquiv.ofBijective (typeICyclicHom ξ)
    ⟨typeICyclicHom_injective hM p hp ξ hξ hpξ,
      typeICyclicHom_surjective hM p hp ξ hξ hpξ⟩

theorem typeICyclicHom_eq_compression (ξ : H) (a : Algebra M) :
    typeICyclicHom ξ a = cornerCompression (typeICyclicSpace M ξ) a.val := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  exact (cornerCompression_coe_of_invariant (typeICyclicSpace M ξ) a.val
    (fun _ hy => vectorOrbitClosure_invariant _ _ a hy) x).symm

/-- Compression to the minimal cyclic space, transported back to the
original factor, is a contractive projection of the ambient operators. -/
theorem IsTypeIFactor.isInjective (hM : IsTypeIFactor M) : IsInjective M := by
  classical
  obtain ⟨p, hp⟩ := hM.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M ξ
  let e : Algebra M ≃⋆ₐ[ℂ] (K →L[ℂ] K) :=
    typeICyclicEquiv hM.factor p hp ξ hξ hpξ
  let F : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
    M.toStarSubalgebra.subtype.toAlgHom.toLinearMap.comp
      (e.symm.toAlgEquiv.toLinearMap.comp (cornerCompression K))
  have he (T : K →L[ℂ] K) : ‖e.symm T‖ = ‖T‖ := by
    rw [← typeICyclicHom_norm hM.factor p hp ξ hξ hpξ]
    change ‖e (e.symm T)‖ = ‖T‖
    rw [e.apply_symm_apply]
  have hF (T : H →L[ℂ] H) : ‖F T‖ ≤ ‖T‖ := by
    change ‖e.symm (cornerCompression K T)‖ ≤ ‖T‖
    rw [he]
    exact norm_cornerCompression_le K T
  let E := F.mkContinuous 1 (fun T => by simpa only [one_mul] using hF T)
  refine ⟨E, E.opNorm_le_bound zero_le_one (fun T => by
    change ‖F T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using hF T), ?_, ?_⟩
  · intro T
    exact (e.symm (cornerCompression K T)).property
  · intro T hT
    let a : Algebra M := ⟨T, hT⟩
    change (e.symm (cornerCompression K a.val)).val = a.val
    rw [← typeICyclicHom_eq_compression]
    change (e.symm (e a)).val = a.val
    rw [e.symm_apply_apply]

/-- The type I injectivity input is an unconditional theorem. -/
theorem publishedTypeIInjectivity : PublishedTypeIInjectivity (H := H) := by
  intro M hM
  exact hM.isInjective

end

end KadisonKastler

end OAI
