import OAI.GroupTheory.PolycyclicRecognition.Lattices.DerivationSolvableModel

namespace OAI

/-! # A solvable Lie model for a smooth real action

The action may have expanding, contracting, or rotational parts. The model
construction needs its actual smooth action, not a nilpotence assumption.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {L : Type} [NormedAddCommGroup L] [NormedSpace ℝ L]
  [FiniteDimensional ℝ L] [Group L] [LieGroup (𝓘(ℝ, L)) ⊤ L]
  [Group.IsSolvable L]
  (φ : Multiplicative ℝ →* MulAut L)
  (hφ : ContDiff ℝ ⊤ (fun p : ℝ × L => φ (Multiplicative.ofAdd p.1) p.2))

def realActionSemidirectEquiv : (L × ℝ) ≃ (L ⋊[φ] Multiplicative ℝ) where
  toFun p := ⟨p.1, Multiplicative.ofAdd p.2⟩
  invFun p := (p.left, p.right.toAdd)
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def realActionSemidirectGroup : Group (L × ℝ) :=
  (realActionSemidirectEquiv φ).group

include hφ

omit [Group.IsSolvable L] [FiniteDimensional ℝ L] in
theorem realActionSemidirectLieGroup :
    letI := realActionSemidirectGroup φ
    LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ) := by
  let := realActionSemidirectGroup φ
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · change ContMDiff ((𝓘(ℝ, L × ℝ)).prod (𝓘(ℝ, L × ℝ)))
      (𝓘(ℝ, L × ℝ)) ⊤ (fun p : (L × ℝ) × (L × ℝ) =>
        (p.1.1 * φ (Multiplicative.ofAdd p.1.2) p.2.1, p.1.2 + p.2.2))
    have hf : ContDiff ℝ ⊤ (fun p : (L × ℝ) × (L × ℝ) =>
        φ (Multiplicative.ofAdd p.1.2) p.2.1) :=
      hφ.comp ((contDiff_fst.snd).prodMk (contDiff_snd.fst))
    have hm : ContMDiff (𝓘(ℝ, (L × ℝ) × (L × ℝ))) (𝓘(ℝ, L)) ⊤
        (fun p : (L × ℝ) × (L × ℝ) => p.1.1 * φ (Multiplicative.ofAdd p.1.2) p.2.1) :=
      (contDiff_fst.fst).contMDiff.mul hf.contMDiff
    exact (hm.contDiff.prodMk ((contDiff_fst.snd).add (contDiff_snd.snd))).comp_contMDiff
      (contMDiff_fst.prodMk_space contMDiff_snd)
  · change ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L × ℝ)) ⊤
      (fun p : L × ℝ => (φ (Multiplicative.ofAdd (-p.2)) (p.1⁻¹), -p.2))
    have hi : ContMDiff (𝓘(ℝ, L × ℝ)) (𝓘(ℝ, L)) ⊤
        (fun p : L × ℝ => p.1⁻¹) := contDiff_fst.contMDiff.inv
    have hf : ContDiff ℝ ⊤ (fun p : L × ℝ =>
        φ (Multiplicative.ofAdd (-p.2)) (p.1⁻¹)) :=
      hφ.comp (contDiff_snd.neg.prodMk hi.contDiff)
    exact (hf.prodMk contDiff_snd.neg).contMDiff

def smoothRealActionModel : SimplyConnectedSolvableLieModel := by
  let g := realActionSemidirectGroup φ
  let : Group (L × ℝ) := g
  let : Mul (L × ℝ) := g.toMul
  let : One (L × ℝ) := g.toOne
  let : Monoid (L × ℝ) := g.toMonoid
  let : MulOneClass (L × ℝ) := g.toMulOneClass
  let : LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ) := realActionSemidirectLieGroup φ hφ
  let e : (L × ℝ) ≃* (L ⋊[φ] Multiplicative ℝ) :=
    { realActionSemidirectEquiv φ with map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (L ⋊[φ] Multiplicative ℝ) := semidirect_solvable φ
  let : Group.IsSolvable (L × ℝ) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact { modelSpace := L × ℝ, carrier := L × ℝ }

def smoothRealActionModelEquiv : (smoothRealActionModel φ hφ).carrier ≃*
    (L ⋊[φ] Multiplicative ℝ) :=
  { realActionSemidirectEquiv φ with map_mul' := fun _ _ => rfl }

attribute [local instance] semidirectProductTopology

theorem smoothRealActionModelEquiv_continuous : Continuous (smoothRealActionModelEquiv φ hφ) := by
  change Continuous ((semidirectProductHomeomorph φ).symm ∘
    (fun p : L × ℝ => (p.1, Multiplicative.ofAdd p.2)))
  exact (semidirectProductHomeomorph φ).symm.continuous.comp continuous_id

theorem smoothRealActionModelEquiv_symm_continuous :
    Continuous (smoothRealActionModelEquiv φ hφ).symm := by
  change Continuous ((fun p : L × Multiplicative ℝ => (p.1, p.2.toAdd)) ∘
    semidirectProductHomeomorph φ)
  exact continuous_id.comp (semidirectProductHomeomorph φ).continuous

end PolycyclicRecognition

end

end OAI
