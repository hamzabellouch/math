import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteUnion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

noncomputable def ambientAction {n : ℕ} (U : Set (Affine n)) (Γ : Type*)
    [Group Γ] [MulAction Γ U] (γ : Γ) (y : Affine n) : Affine n :=
  if hy : y ∈ U then (γ • (⟨y,hy⟩ : U)).val else y

@[simp] lemma ambientAction_subtype {n : ℕ} {U : Set (Affine n)} {Γ : Type*}
    [Group Γ] [MulAction Γ U] (γ : Γ) (y : U) :
    ambientAction U Γ γ y.val = (γ • y).val := by
  simp only [ambientAction,dite_eq_left y.property]

noncomputable def actionLocalSet {n : ℕ} (U : Set (Affine n)) (Γ : Type*)
    [Group Γ] [MulAction Γ U] (γ : Γ) (Ω : Set (Affine n)) : Set (Affine n) :=
  U ∩ (ambientAction U Γ γ) ⁻¹' Ω

lemma actionLocalSet_subset {n : ℕ} {U : Set (Affine n)} {Γ : Type*}
    [Group Γ] [MulAction Γ U] (γ : Γ) (Ω : Set (Affine n)) :
    actionLocalSet U Γ γ Ω ⊆ U := inter_subset_left

lemma actionLocalSet_open {n : ℕ} {U : Set (Affine n)} {Γ : Type*}
    [Group Γ] [MulAction Γ U] [ContinuousConstSMul Γ U]
    (γ : Γ) {Ω : Set (Affine n)}
    (hΩ : IsOpen ((Subtype.val : U → Affine n) ⁻¹' Ω)) :
    IsOpen ((Subtype.val : U → Affine n) ⁻¹' actionLocalSet U Γ γ Ω) := by
  have he : (Subtype.val : U → Affine n) ⁻¹' actionLocalSet U Γ γ Ω =
      (fun y : U => γ • y) ⁻¹' ((Subtype.val : U → Affine n) ⁻¹' Ω) := by
    ext y
    simp only [actionLocalSet,mem_preimage,mem_inter_iff,y.property,true_and,
      ambientAction_subtype]
  rw [he]
  exact hΩ.preimage (continuous_const_smul γ)

noncomputable def normalizedLocalBiholomorph {n m : ℕ} {U Ω : Set (Affine n)}
    {D : Set (Affine m)} {Γ : Type*} [Group Γ] [MulAction Γ U]
    [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (γ : Γ) (b : Biholomorph (U ∩ Ω) D) :
    Biholomorph (actionLocalSet U Γ γ Ω) D :=
  ((actionBiholomorph U Γ hhol γ).restrict
    (actionLocalSet_subset γ Ω) inter_subset_left (by
      intro y
      simp only [actionLocalSet,mem_inter_iff,mem_preimage,y.property,
        ambientAction_subtype,true_and]
      exact (and_iff_right (γ • y).property).symm)).trans b

lemma normalizedLocalBiholomorph_forward {n m : ℕ} {U Ω : Set (Affine n)}
    {D : Set (Affine m)} {Γ : Type*} [Group Γ] [MulAction Γ U]
    [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (γ : Γ) (b : Biholomorph (U ∩ Ω) D) (f : Affine n → Affine m)
    (hf : ∀ y : ↥(U ∩ Ω), f y.val=(b.toHomeomorph y).val)
    (y : actionLocalSet U Γ γ Ω) :
    f (ambientAction U Γ γ y.val) =
      ((normalizedLocalBiholomorph hhol γ b).toHomeomorph y).val := by
  have he : ambientAction U Γ γ y.val = (γ • (⟨y.val,y.property.1⟩ : U)).val := by
    exact ambientAction_subtype γ ⟨y.val,y.property.1⟩
  rw [he]
  exact hf ⟨(γ • (⟨y.val,y.property.1⟩ : U)).val,
    ⟨(γ • (⟨y.val,y.property.1⟩ : U)).property,he ▸ y.property.2⟩⟩

lemma normalizedLocalBiholomorph_inverse {n m : ℕ} {U Ω : Set (Affine n)}
    {D : Set (Affine m)} {Γ : Type*} [Group Γ] [MulAction Γ U]
    [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (γ : Γ) (b : Biholomorph (U ∩ Ω) D) (g : Affine m → Affine n)
    (hg : ∀ y : D, g y.val=(b.toHomeomorph.symm y).val) (y : D) :
    ambientAction U Γ γ⁻¹ (g y.val) =
      ((normalizedLocalBiholomorph hhol γ b).toHomeomorph.symm y).val := by
  rw [hg y]
  exact ambientAction_subtype γ⁻¹ ⟨(b.toHomeomorph.symm y).val,
    (b.toHomeomorph.symm y).property.1⟩

end Release061

end

end OAI
