import OAI.RepresentationTheory.FoulkesHowe.Actions
import OAI.RepresentationTheory.FoulkesHowe.Spanning

namespace OAI

noncomputable section
open scoped BigOperators
universe u v w
namespace Problem346

variable {V : Type u} {W : Type v} {U : Type w}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

/-- The map on a plethysm induced by a linear map on the original space. -/
def plethysmMap (outer inner : ℕ) (f : V →ₗ[ℂ] W) :
    SymPow outer (SymPow inner V) →ₗ[ℂ] SymPow outer (SymPow inner W) :=
  symPowMap outer (symPowMap inner f)

@[simp] theorem plethysmMap_symMonomial (outer inner : ℕ) (f : V →ₗ[ℂ] W)
    (x : Fin outer → Fin inner → V) :
    plethysmMap outer inner f
        (symMonomial outer (SymPow inner V) (fun i => symMonomial inner V (x i))) =
      symMonomial outer (SymPow inner W)
        (fun i => symMonomial inner W (fun j => f (x i j))) := by
  simp [plethysmMap]

@[simp] theorem plethysmMap_id (outer inner : ℕ) :
    plethysmMap outer inner (LinearMap.id : V →ₗ[ℂ] V) = LinearMap.id := by
  simp [plethysmMap]

@[simp] theorem plethysmMap_comp (outer inner : ℕ) (g : W →ₗ[ℂ] U) (f : V →ₗ[ℂ] W) :
    plethysmMap outer inner (g.comp f) =
      (plethysmMap outer inner g).comp (plethysmMap outer inner f) := by
  simp [plethysmMap]

@[simp] theorem plethysmMap_equiv (outer inner : ℕ) (g : V ≃ₗ[ℂ] V) :
    plethysmMap outer inner g.toLinearMap = plethysmAction outer inner g := rfl

/-- The explicitly normalized Foulkes formula is natural in the vector space. -/
theorem plethysmMap_foulkesFormula (a b : ℕ) (f : V →ₗ[ℂ] W)
    (x : Fin b → Fin a → V) :
    plethysmMap a b f (foulkesFormula a b V x) =
      foulkesFormula a b W (fun j i => f (x j i)) := by
  classical
  unfold foulkesFormula
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact plethysmMap_symMonomial a b f (fun i j => x j ((σ j) i))

/-- Any two maps satisfying the canonical formula form a natural square. -/
theorem IsFoulkesMap.natural {a b : ℕ}
    {μV : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    {μW : SymPow b (SymPow a W) →ₗ[ℂ] SymPow a (SymPow b W)}
    (hV : IsFoulkesMap a b V μV) (hW : IsFoulkesMap a b W μW)
    (f : V →ₗ[ℂ] W) :
    (plethysmMap a b f).comp μV = μW.comp (plethysmMap b a f) := by
  apply plethysm_linearMap_ext a b V
  intro x
  simp only [LinearMap.comp_apply, plethysmMap_symMonomial]
  rw [hV, hW, plethysmMap_foulkesFormula]

/-- Every canonical Foulkes map is GL-equivariant. -/
theorem IsFoulkesMap.commutes {a b : ℕ}
    {μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V)}
    (hμ : IsFoulkesMap a b V μ) (g : V ≃ₗ[ℂ] V) :
    (plethysmAction a b g).comp μ = μ.comp (plethysmAction b a g) :=
  hμ.natural hμ g.toLinearMap

end Problem346

end

end OAI
