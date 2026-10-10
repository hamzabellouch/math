import Mathlib
import OAI.Analysis.Commutator.CornerCyclicImplementation

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerImplementation

open ConcreteCorner ReducingRepresentation

variable {H ι : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (M : VonNeumannAlgebra H)

lemma cyclic_dense (ξ : H) :
    DenseRange (fun a : Algebra M =>
      restrict (inclusion M) (cyclicSubspace M.toStarSubalgebra ξ)
        (fun a => cyclicSubspace_invariant M.toStarSubalgebra ξ a.property) a
        ⟨ξ,mem_cyclicSubspace_self M.toStarSubalgebra ξ⟩) := by
  let K := cyclicSubspace M.toStarSubalgebra ξ
  let act : Algebra M → K := fun a =>
    ⟨(a:H →L[ℂ] H) ξ,cyclicSubspace_invariant M.toStarSubalgebra ξ a.property ξ
      (mem_cyclicSubspace_self M.toStarSubalgebra ξ)⟩
  have hi : (Subtype.val : K → H) '' Set.range act =
      (orbitSubmodule M.toStarSubalgebra ξ : Set H) := by
    ext x
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨act ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,rfl⟩
  intro x
  change x∈closure (Set.range act)
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hi]
  exact x.property

theorem exists_local_module {p : Algebra M} (hp : IsStarProjection p)
    (v : ι → Algebra M)
    (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
    (hinit : ∀ i, p*star (v i)=star (v i))
    (htotal : ∑ i, v i*star (v i)=1)
    (G : H →L[ℂ] H)
    (hGp : G.comp (inclusion M p)=(inclusion M p).comp G)
    (hGv : ∀ i, G.comp (inclusion M (v i))=(inclusion M (v i)).comp G)
    (ξ : H) (hpξ : inclusion M p ξ=ξ)
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : Corner hp,
      ‖G.comp (inclusion M (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖) :
    ∃ T : H →L[ℂ] H,
      (∀ a : Algebra M, T.comp (inclusion M a)=(inclusion M a).comp T) ∧
      ∀ z∈cyclicSubspace M.toStarSubalgebra ξ, ‖G z-T z‖≤(16*ε)*‖z‖ := by
  let K := cyclicSubspace M.toStarSubalgebra ξ
  let hinv : ∀ (a : Algebra M) (x : H), x∈K → inclusion M a x∈K :=
    fun a => cyclicSubspace_invariant M.toStarSubalgebra ξ a.property
  let σ := restrict (inclusion M) K hinv
  let j : K →ₗᵢ[ℂ] H := K.subtypeₗᵢ
  have hj (a : Algebra M) (x : K) : j (σ a x)=inclusion M a (j x) := rfl
  have hGp' (x : K) : (G.comp K.subtypeL) (σ p x)=inclusion M p ((G.comp K.subtypeL) x) :=
    congrArg (fun F : H →L[ℂ] H => F (x:H)) hGp
  have hGv' (i : ι) (x : K) : (G.comp K.subtypeL) (σ (v i) x)=
      inclusion M (v i) ((G.comp K.subtypeL) x) :=
    congrArg (fun F : H →L[ℂ] H => F (x:H)) (hGv i)
  let Ω : K := ⟨ξ,mem_cyclicSubspace_self M.toStarSubalgebra ξ⟩
  have hδ' (a : Corner hp) :
      ‖(G.comp K.subtypeL).comp (σ (a:Algebra M))-
        (inclusion M (a:Algebra M)).comp (G.comp K.subtypeL)‖≤ε*‖a‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg a))
    intro x
    change ‖G (inclusion M (a:Algebra M) (x:H))-inclusion M (a:Algebra M) (G (x:H))‖≤_
    exact ((G.comp (inclusion M (a:Algebra M))-(inclusion M (a:Algebra M)).comp G).le_opNorm (x:H)).trans
      (mul_le_mul_of_nonneg_right (hδ a) (norm_nonneg _))
  obtain ⟨T,hT,hn⟩ := exists_matrix_corner_intertwiner M σ j hj hp
    (G.comp K.subtypeL) hGp' v hcol hinit htotal hGv' Ω (cyclic_dense M ξ)
    (Subtype.ext hpξ) hε hδ'
  refine ⟨extendZero (K := K) T,extendZero_intertwines (inclusion M) (inclusion M) K hinv T hT,?_⟩
  intro z hz
  exact norm_sub_extendZero_apply_le K G T (16*ε) hn ⟨z,hz⟩

end Kadison.MatrixCornerImplementation

end

end
end

end OAI
