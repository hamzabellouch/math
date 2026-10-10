import OAI.Analysis.KadisonKastler.PairedAmplification
import OAI.Analysis.KadisonKastler.StarEquivTraceTransport
import OAI.Analysis.FactorGeneration.TraceTransport

namespace OAI

/-! # The concrete factor in the paired diagonal representation

The two finite traces identify every strong limit of paired operators.
Consequently the paired range equals its bicommutant, and the source
factor is isomorphic to this actual concrete von Neumann algebra.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- The actual paired representation on the two-fold Hilbert sum. -/
def pairedFactorHom (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    Algebra M →⋆ₐ[ℂ] (Generator.FiniteHilbert (Fin 2) H →L[ℂ]
      Generator.FiniteHilbert (Fin 2) H) :=
  hilbertMatrixHom.comp (pairedRepresentation M.toStarSubalgebra.subtype
    (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))

theorem pairedFactorHom_apply_zero (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (a : Algebra M) (ξ : Generator.FiniteHilbert (Fin 2) H) :
    pairedFactorHom θ a ξ 0 = a.val (ξ 0) := by
  simp [pairedFactorHom, StarAlgHom.comp_apply, pairedRepresentation_apply,
    hilbertMatrixHom, hilbertMatrix_apply, blockDiagonal, diagonalStarAlgHom_apply,
    Fin.sum_univ_two]

theorem pairedFactorHom_apply_one (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (a : Algebra M) (ξ : Generator.FiniteHilbert (Fin 2) H) :
    pairedFactorHom θ a ξ 1 = (θ a).val (ξ 1) := by
  simp [pairedFactorHom, StarAlgHom.comp_apply, pairedRepresentation_apply,
    hilbertMatrixHom, hilbertMatrix_apply, blockDiagonal, diagonalStarAlgHom_apply,
    Fin.sum_univ_two]

theorem pairedFactorHom_injective (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    Function.Injective (pairedFactorHom θ) := by
  intro a b hab
  apply Subtype.ext
  ext ξ
  have h := congrArg (fun T : Generator.FiniteHilbert (Fin 2) H →L[ℂ]
    Generator.FiniteHilbert (Fin 2) H => T (Generator.tupleSingle 0 ξ) 0) hab
  simpa only [pairedFactorHom_apply_zero, Generator.tupleSingle_apply,
    Pi.single_eq_same] using h

/-- A strong limit of paired operators is again paired. The trace tests
are finite sums of vector coefficients, so no uniform norm bound is needed. -/
theorem pairedFactorHom_range_strong_closed
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {I : Type*} {l : Filter I} [l.NeBot] (a : I → Algebra M)
    (T : Generator.FiniteHilbert (Fin 2) H →L[ℂ] Generator.FiniteHilbert (Fin 2) H)
    (hT : ∀ ξ, Tendsto (fun i => pairedFactorHom θ (a i) ξ) l (𝓝 (T ξ))) :
    T ∈ (pairedFactorHom θ).range := by
  let A : H →L[ℂ] H := Generator.operatorEntry T 0 0
  let B : H →L[ℂ] H := Generator.operatorEntry T 1 1
  have hA (ξ : H) : Tendsto (fun i => (a i).val ξ) l (𝓝 (A ξ)) := by
    have h := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) 0).continuous.tendsto _).comp
      (hT (Generator.tupleSingle 0 ξ))
    change Tendsto (fun i => pairedFactorHom θ (a i) (Generator.tupleSingle 0 ξ) 0) l
      (𝓝 (A ξ)) at h
    simpa only [pairedFactorHom_apply_zero, Generator.tupleSingle_apply,
      Pi.single_eq_same] using h
  have hB (ξ : H) : Tendsto (fun i => (θ (a i)).val ξ) l (𝓝 (B ξ)) := by
    have h := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) 1).continuous.tendsto _).comp
      (hT (Generator.tupleSingle 1 ξ))
    change Tendsto (fun i => pairedFactorHom θ (a i) (Generator.tupleSingle 1 ξ) 1) l
      (𝓝 (B ξ)) at h
    simpa only [pairedFactorHom_apply_one, Generator.tupleSingle_apply,
      Pi.single_eq_same] using h
  have hAm : A ∈ M := Generator.Tracial.weak_operator_limit_mem M a A (fun ξ η =>
    tendsto_const_nhds.inner (hA ξ))
  have hBm : B ∈ N := Generator.Tracial.weak_operator_limit_mem N (fun i => θ (a i)) B
    (fun ξ η => tendsto_const_nhds.inner (hB ξ))
  let x : Algebra M := ⟨A, hAm⟩
  let y : Algebra N := ⟨B, hBm⟩
  have hpair (c : Algebra M) :
      τN.toLinearMap (θ c * y) = τM.toLinearMap (c * x) := by
    have hleft : Tendsto (fun i => τM.toLinearMap (c * a i)) l
        (𝓝 (τM.toLinearMap (c * x))) := by
      apply hτM.tendsto
      intro ξ η
      exact tendsto_const_nhds.inner ((c.val.continuous.tendsto _).comp (hA ξ))
    have hright : Tendsto (fun i => τN.toLinearMap (θ c * θ (a i))) l
        (𝓝 (τN.toLinearMap (θ c * y))) := by
      apply hτN.tendsto
      intro ξ η
      exact tendsto_const_nhds.inner (((θ c).val.continuous.tendsto _).comp (hB ξ))
    have he (i : I) : τN.toLinearMap (θ c * θ (a i)) = τM.toLinearMap (c * a i) := by
      rw [← map_mul]
      exact trace_starAlgEquiv hM τM τN θ _
    exact tendsto_nhds_unique (hright.congr (fun i => he i)) hleft
  have hy : y = θ x := by
    let d := y - θ x
    let c := θ.symm (star d)
    have hp := hpair c
    have ht := trace_starAlgEquiv hM τM τN θ (c * x)
    rw [map_mul] at ht
    have hz : τN.toLinearMap (star d * d) = 0 := by
      have hcd : θ c = star d := θ.apply_symm_apply _
      rw [hcd] at hp ht
      change τN.toLinearMap (star d * (y - θ x)) = 0
      rw [mul_sub, map_sub, hp, ht, sub_self]
    exact sub_eq_zero.mp (τN.faithful d hz)
  refine ⟨x, ?_⟩
  ext ξ j
  fin_cases j
  · change pairedFactorHom θ x ξ 0 = T ξ 0
    rw [pairedFactorHom_apply_zero]
    have ht := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) 0).continuous.tendsto _).comp (hT ξ)
    change Tendsto (fun i => pairedFactorHom θ (a i) ξ 0) l (𝓝 (T ξ 0)) at ht
    simp only [pairedFactorHom_apply_zero] at ht
    exact tendsto_nhds_unique (hA (ξ 0)) ht
  · change pairedFactorHom θ x ξ 1 = T ξ 1
    rw [pairedFactorHom_apply_one]
    have ht := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) 1).continuous.tendsto _).comp (hT ξ)
    change Tendsto (fun i => pairedFactorHom θ (a i) ξ 1) l (𝓝 (T ξ 1)) at ht
    simp only [pairedFactorHom_apply_one] at ht
    have hb := hB (ξ 1)
    have hxy : (θ x).val = B := congrArg Subtype.val hy.symm
    rw [← hxy] at hb
    exact tendsto_nhds_unique hb ht

theorem pairedFactorHom_bicommutant
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    Set.centralizer (Set.centralizer ((pairedFactorHom θ).range : Set (Generator.FiniteHilbert (Fin 2) H →L[ℂ]
      Generator.FiniteHilbert (Fin 2) H))) =
      ((pairedFactorHom θ).range : Set (Generator.FiniteHilbert (Fin 2) H →L[ℂ]
      Generator.FiniteHilbert (Fin 2) H)) := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net (pairedFactorHom θ).range T hT
    choose x hx using fun i => (a i).property
    apply pairedFactorHom_range_strong_closed hM τM τN hτM hτN θ (l := atTop) x T
    intro ξ
    exact (ha ξ).congr (fun i => congrArg (fun S => S ξ) (hx i).symm)
  · intro T hT S hS
    exact (hS T hT).symm

/-- The actual von Neumann algebra on the original two-fold Hilbert sum. -/
def pairedVonNeumann
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    VonNeumannAlgebra (Generator.FiniteHilbert (Fin 2) H) where
  toStarSubalgebra := (pairedFactorHom θ).range
  centralizer_centralizer' := pairedFactorHom_bicommutant hM
    (concreteFactorTrace hM) (concreteFactorTrace hN)
    (concreteFactorTrace_finiteVector hM) (concreteFactorTrace_finiteVector hN) θ

/-- The source algebra is isomorphic to its concrete paired image. -/
def pairedFactorEquiv
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (pairedVonNeumann hM hN θ) :=
  StarAlgEquiv.ofInjective (pairedFactorHom θ) (pairedFactorHom_injective θ)

theorem pairedFactorEquiv_apply
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (x : Algebra M) :
    (pairedFactorEquiv hM hN θ x).val =
      hilbertMatrix (pairedRepresentation M.toStarSubalgebra.subtype
        (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom) x) := rfl

theorem pairedVonNeumann_isII1
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    Generator.IsII1Factor (pairedVonNeumann hM hN θ).toStarSubalgebra :=
  Generator.isII1Factor_of_starAlgEquiv (pairedFactorEquiv hM hN θ) hM
    (Generator.Tracial.traceHilbertVonNeumann_wotClosed (pairedVonNeumann hM hN θ))

local instance pairedFactorSourceOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance pairedFactorSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance pairedFactorImageOrder
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    PartialOrder (Algebra (pairedVonNeumann hM hN θ)) := CStarAlgebra.spectralOrder _
local instance pairedFactorImageStarOrder
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    StarOrderedRing (Algebra (pairedVonNeumann hM hN θ)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Uniform closeness of an isomorphism between concrete finite factors is
complete closeness, with the paired factor constructed above. -/
theorem complete_closeness_of_finiteFactor_equiv [TopologicalSpace.SeparableSpace H]
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (hCyclic : PublishedCyclicSimilarity.{u, u}
      (A := Algebra (pairedVonNeumann hM hN θ)))
    (hFock : PublishedDiagonalFockRepresentation.{u})
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ x : Algebra M, ‖x.val - (θ x).val‖ ≤ δ * ‖x‖) :
    CompletelyBoundedBy (M.toStarSubalgebra.subtype.toLinearMap -
      (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom).toAlgHom.toLinearMap)
      (600 * δ) := by
  exact complete_closeness_of_paired_factor hpub hmat hind
    (pairedVonNeumann_isII1 hM hN θ) hCyclic hFock
    M.toStarSubalgebra.subtype (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom)
    (pairedFactorEquiv hM hN θ) (pairedFactorEquiv_apply hM hN θ) hδ hclose

end

end KadisonKastler

end OAI
