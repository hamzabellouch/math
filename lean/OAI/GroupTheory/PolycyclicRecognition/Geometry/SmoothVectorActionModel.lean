import OAI.GroupTheory.PolycyclicRecognition.Lattices.DerivationSolvableModel

namespace OAI

/-! # A solvable Lie model for a smooth vector action

The acting vector space may have any finite dimension. The actual smooth
action supplies the multiplication and inverse on the product manifold.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {L V : Type} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [FiniteDimensional ℝ L] [Group L] [LieGroup (𝓘(ℝ, L)) ⊤ L]
  [Group.IsSolvable L]
  (φ : Multiplicative V →* MulAut L)
  (hφ : ContDiff ℝ ⊤ (fun p : V × L => φ (Multiplicative.ofAdd p.1) p.2))

def vectorActionSemidirectEquiv : (L × V) ≃ (L ⋊[φ] Multiplicative V) where
  toFun p := ⟨p.1, Multiplicative.ofAdd p.2⟩
  invFun p := (p.left, p.right.toAdd)
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def vectorActionSemidirectGroup : Group (L × V) :=
  (vectorActionSemidirectEquiv φ).group

include hφ

omit [Group.IsSolvable L] [FiniteDimensional ℝ L] [FiniteDimensional ℝ V] in
theorem vectorActionSemidirectLieGroup :
    letI := vectorActionSemidirectGroup φ
    LieGroup (𝓘(ℝ, L × V)) ⊤ (L × V) := by
  let := vectorActionSemidirectGroup φ
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · change ContMDiff ((𝓘(ℝ, L × V)).prod (𝓘(ℝ, L × V)))
      (𝓘(ℝ, L × V)) ⊤ (fun p : (L × V) × (L × V) =>
        (p.1.1 * φ (Multiplicative.ofAdd p.1.2) p.2.1, p.1.2 + p.2.2))
    have hf : ContDiff ℝ ⊤ (fun p : (L × V) × (L × V) =>
        φ (Multiplicative.ofAdd p.1.2) p.2.1) :=
      hφ.comp ((contDiff_fst.snd).prodMk (contDiff_snd.fst))
    have hm : ContMDiff (𝓘(ℝ, (L × V) × (L × V))) (𝓘(ℝ, L)) ⊤
        (fun p : (L × V) × (L × V) => p.1.1 * φ (Multiplicative.ofAdd p.1.2) p.2.1) :=
      (contDiff_fst.fst).contMDiff.mul hf.contMDiff
    exact (hm.contDiff.prodMk ((contDiff_fst.snd).add (contDiff_snd.snd))).comp_contMDiff
      (contMDiff_fst.prodMk_space contMDiff_snd)
  · change ContMDiff (𝓘(ℝ, L × V)) (𝓘(ℝ, L × V)) ⊤
      (fun p : L × V => (φ (Multiplicative.ofAdd (-p.2)) (p.1⁻¹), -p.2))
    have hi : ContMDiff (𝓘(ℝ, L × V)) (𝓘(ℝ, L)) ⊤
        (fun p : L × V => p.1⁻¹) := contDiff_fst.contMDiff.inv
    have hf : ContDiff ℝ ⊤ (fun p : L × V =>
        φ (Multiplicative.ofAdd (-p.2)) (p.1⁻¹)) :=
      hφ.comp (contDiff_snd.neg.prodMk hi.contDiff)
    exact (hf.prodMk contDiff_snd.neg).contMDiff

def smoothVectorActionModel : SimplyConnectedSolvableLieModel := by
  let g := vectorActionSemidirectGroup φ
  let : Group (L × V) := g
  let : Mul (L × V) := g.toMul
  let : One (L × V) := g.toOne
  let : Monoid (L × V) := g.toMonoid
  let : MulOneClass (L × V) := g.toMulOneClass
  let : LieGroup (𝓘(ℝ, L × V)) ⊤ (L × V) := vectorActionSemidirectLieGroup φ hφ
  let e : (L × V) ≃* (L ⋊[φ] Multiplicative V) :=
    { vectorActionSemidirectEquiv φ with map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (L ⋊[φ] Multiplicative V) := semidirect_solvable φ
  let : Group.IsSolvable (L × V) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact { modelSpace := L × V, carrier := L × V }

def smoothVectorActionModelEquiv : (smoothVectorActionModel φ hφ).carrier ≃*
    (L ⋊[φ] Multiplicative V) :=
  { vectorActionSemidirectEquiv φ with map_mul' := fun _ _ => rfl }

attribute [local instance] semidirectProductTopology

theorem smoothVectorActionModelEquiv_continuous : Continuous (smoothVectorActionModelEquiv φ hφ) := by
  change Continuous ((semidirectProductHomeomorph φ).symm ∘
    (fun p : L × V => (p.1, Multiplicative.ofAdd p.2)))
  exact (semidirectProductHomeomorph φ).symm.continuous.comp continuous_id

theorem smoothVectorActionModelEquiv_symm_continuous :
    Continuous (smoothVectorActionModelEquiv φ hφ).symm := by
  change Continuous ((fun p : L × Multiplicative V => (p.1, p.2.toAdd)) ∘
    semidirectProductHomeomorph φ)
  exact continuous_id.comp (semidirectProductHomeomorph φ).continuous

end PolycyclicRecognition

end

end OAI
