import Mathlib
import OAI.Analysis.WeakInfiniteness.PureIrreducible

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u v

open scoped ComplexOrder InnerProductSpace Topology

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem extreme_norming_state_representation [Nontrivial A] (b : A) (hb : 0 ≤ b) :
    ∃ (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ (realStateSpace A).extremePoints ℝ),
      ‖(realStateComplexification f hf.1).gnsStarAlgHom b‖=‖b‖ := by
  obtain ⟨f,hf,hfb⟩ := exists_extreme_norming_real_state b hb
  refine ⟨f,hf,le_antisymm
    (NonUnitalStarAlgHom.norm_apply_le (realStateComplexification f hf.1).gnsNonUnitalStarAlgHom b) ?_⟩
  let Φ := realStateComplexification f hf.1
  let Ω := gnsCyclicVector Φ
  have hΩ : ‖Ω‖=1 := norm_gnsCyclicVector Φ (realStateComplexification_one f hf.1)
  have hv : (inner ℂ Ω (Φ.gnsStarAlgHom b Ω)).re=‖b‖ := by
    have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1) ⟨b,hb.isSelfAdjoint⟩
    exact he.trans hfb
  calc
    ‖b‖ = (inner ℂ Ω (Φ.gnsStarAlgHom b Ω)).re := hv.symm
    _ ≤ ‖inner ℂ Ω (Φ.gnsStarAlgHom b Ω)‖ := Complex.re_le_norm _
    _ ≤ ‖Ω‖*‖Φ.gnsStarAlgHom b Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖*(‖Φ.gnsStarAlgHom b‖*‖Ω‖) := by
      gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Φ.gnsStarAlgHom b‖ := by rw [hΩ,one_mul,mul_one]

end Unital

section NonUnital

variable {A : Type u} {H : Type v} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def NonUnitalRepresentationIrreducible (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H,IsClosed (S : Set H) →
    (∀ a : A,∀ x ∈ S,π a x ∈ S) → S=⊥ ∨ S=⊤

lemma irreducible_restrict_unitization
    (π : Unitization ℂ A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : RepresentationIrreducible π) :
    NonUnitalRepresentationIrreducible
      (π.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)) := by
  intro S hSc hS
  apply hπ S hSc
  intro u x hx
  rw [← Unitization.inl_fst_add_inr_snd_eq u,map_add, ← Unitization.algebraMap_eq_inl]
  have hc : π (algebraMap ℂ (Unitization ℂ A) u.fst) =
      algebraMap ℂ (H →L[ℂ] H) u.fst := AlgHomClass.commutes π _
  rw [hc]
  change u.fst • x+π (Unitization.inr u.snd) x ∈ S
  exact S.add_mem (S.smul_mem _ hx) (hS _ _ hx)

variable [PartialOrder A] [StarOrderedRing A]

theorem exists_irreducible_norming_representation (b : A) (hb : 0 ≤ b) (hb0 : b ≠ 0) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π ∧ ‖π b‖=‖b‖ ∧ π b ≠ 0 := by
  let u : Unitization ℂ A := (b : Unitization ℂ A)
  have hu : 0 ≤ u := by
    change 0 ≤ (Unitization.inrNonUnitalStarAlgHom ℂ A) b
    exact map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) hb
  obtain ⟨f,hf,hfn⟩ := extreme_norming_state_representation u hu
  let Φ := realStateComplexification f hf.1
  let π := Φ.gnsStarAlgHom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hn : ‖π b‖=‖b‖ := by
    change ‖Φ.gnsStarAlgHom u‖=‖b‖
    rw [hfn]
    exact Unitization.norm_inr b
  refine ⟨Φ.GNS,inferInstance,inferInstance,inferInstance,π,
    irreducible_restrict_unitization Φ.gnsStarAlgHom (extreme_real_state_gns_irreducible f hf),hn,?_⟩
  intro hz
  have : ‖b‖=0 := by rw [← hn,hz,norm_zero]
  exact hb0 (norm_eq_zero.mp this)

end NonUnital

end

end WeakPureInfiniteness
end

end OAI
