import OAI.RepresentationTheory.FoulkesHowe.Naturality
import OAI.RepresentationTheory.FoulkesHowe.FiniteDimension
import OAI.RepresentationTheory.FoulkesHowe.DualEmbedding

namespace OAI

/-!
# Lifting perfect duality through a symmetric power

Composition of perfect pairings is separate from construction of the one-level pairing.  Supplying the one-level duality
charts and their naturality gives the duality and adjoint-action identities for
nested symmetric powers.
-/

noncomputable section

namespace Problem346
namespace PlethysmDual

universe u v
variable {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Lift a perfect-duality chart through a symmetric power using the canonical
    duality chart for that symmetric power. -/
def liftDualEquiv (n : ℕ) (e : W ≃ₗ[ℂ] Module.Dual ℂ V)
    (d : SymPow n (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow n V)) :
    SymPow n W ≃ₗ[ℂ] Module.Dual ℂ (SymPow n V) :=
  (symPowEquiv n e).trans d

/-- Adjointness is preserved when a perfect pairing is lifted through a
    symmetric power whose duality chart is natural for the given map. -/
theorem liftDualEquiv_adjoint (n : ℕ) (e : W ≃ₗ[ℂ] Module.Dual ℂ V)
    (d : SymPow n (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow n V))
    (A : V →ₗ[ℂ] V) (A' : W →ₗ[ℂ] W)
    (he : ∀ x y, e (A' x) y = e x (A y))
    (hd : ∀ x y, d (symPowMap n A.dualMap x) y = d x (symPowMap n A y))
    (x : SymPow n W) (y : SymPow n V) :
    liftDualEquiv n e d (symPowMap n A' x) y =
      liftDualEquiv n e d x (symPowMap n A y) := by
  have heq : e.toLinearMap.comp A' = A.dualMap.comp e.toLinearMap := by
    ext x y
    exact he x y
  have hlift : (symPowMap n e.toLinearMap).comp (symPowMap n A') =
      (symPowMap n A.dualMap).comp (symPowMap n e.toLinearMap) := by
    rw [← symPowMap_comp, ← symPowMap_comp, heq]
  change d (symPowMap n e.toLinearMap (symPowMap n A' x)) y =
    d (symPowMap n e.toLinearMap x) (symPowMap n A y)
  have hpoint := LinearMap.congr_fun hlift x
  simp only [LinearMap.comp_apply] at hpoint
  rw [hpoint]
  exact hd _ _

/-- The duality chart for a plethysm is the composite of its inner and outer
    one-level duality charts. -/
def plethysmDualEquivOf (outer inner : ℕ)
    (e : SymPow inner (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow inner V))
    (d : SymPow outer (Module.Dual ℂ (SymPow inner V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow outer (SymPow inner V))) :
    SymPow outer (SymPow inner (Module.Dual ℂ V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow outer (SymPow inner V)) :=
  liftDualEquiv outer e d

/-- Naturality of each level gives the adjoint-action identity for the
    plethysm pairing.  The dual automorphism here is the ordinary dual map,
    not the inverse contragredient; this is precisely the adjoint identity. -/
theorem plethysmDualEquivOf_adjoint (outer inner : ℕ)
    (e : SymPow inner (Module.Dual ℂ V) ≃ₗ[ℂ] Module.Dual ℂ (SymPow inner V))
    (d : SymPow outer (Module.Dual ℂ (SymPow inner V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow outer (SymPow inner V)))
    (g : V ≃ₗ[ℂ] V)
    (he : ∀ x y, e (symPowMap inner g.dualMap.toLinearMap x) y =
      e x (symPowMap inner g.toLinearMap y))
    (hd : ∀ x y,
      d (symPowMap outer (symPowMap inner g.toLinearMap).dualMap x) y =
      d x (symPowMap outer (symPowMap inner g.toLinearMap) y))
    (x : SymPow outer (SymPow inner (Module.Dual ℂ V)))
    (y : SymPow outer (SymPow inner V)) :
    plethysmDualEquivOf outer inner e d
      (plethysmAction outer inner g.dualMap x) y =
    plethysmDualEquivOf outer inner e d x (plethysmAction outer inner g y) := by
  exact liftDualEquiv_adjoint outer e d
    (symPowMap inner g.toLinearMap) (symPowMap inner g.dualMap.toLinearMap)
    he hd x y

/-- The comparison embedding follows formally from a surjection on the dual
    vector space and compatible perfect pairings on the two plethysms. -/
theorem exists_embedding_of_dual_surjection (a b : ℕ)
    [Module.IsReflexive ℂ (SymPow b (SymPow a V))]
    [Module.IsReflexive ℂ (SymPow a (SymPow b V))]
    (e : SymPow b (SymPow a (Module.Dual ℂ V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow b (SymPow a V)))
    (f : SymPow a (SymPow b (Module.Dual ℂ V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow a (SymPow b V)))
    (he : ∀ (g : V ≃ₗ[ℂ] V) x y,
      e (plethysmAction b a g.dualMap x) y = e x (plethysmAction b a g y))
    (hf : ∀ (g : V ≃ₗ[ℂ] V) x y,
      f (plethysmAction a b g.dualMap x) y = f x (plethysmAction a b g y))
    (μ : SymPow b (SymPow a (Module.Dual ℂ V)) →ₗ[ℂ]
      SymPow a (SymPow b (Module.Dual ℂ V)))
    (hμ : Function.Surjective μ)
    (hcomm : ∀ g : V ≃ₗ[ℂ] V,
      μ.comp (plethysmAction b a g.dualMap) =
        (plethysmAction a b g.dualMap).comp μ) :
    ∃ ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V),
      IsGLEquivariantEmbedding a b V ι := by
  let e' := DualEmbedding.flipPairing e
  let f' := DualEmbedding.flipPairing f
  let ι := DualEmbedding.transpose e' f' μ
  refine ⟨ι, isGLEquivariantEmbedding_of_commutes ι
    (DualEmbedding.transpose_injective e' f' μ hμ) ?_⟩
  intro g
  apply DualEmbedding.transpose_intertwines e' f' μ
    (plethysmAction b a g) (plethysmAction b a g.dualMap)
    (plethysmAction a b g) (plethysmAction a b g.dualMap)
  · intro x z
    exact (he g z x).symm
  · intro y w
    exact (hf g w y).symm
  · exact hcomm g

/-- With finite-dimensionality and canonical-map naturality available, only the
    two perfect-duality charts and their adjointness remain to construct the
    comparison embedding from canonical surjectivity on the dual space. -/
theorem comparison_of_dual_charts (a b : ℕ) [FiniteDimensional ℂ V]
    (e : SymPow b (SymPow a (Module.Dual ℂ V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow b (SymPow a V)))
    (f : SymPow a (SymPow b (Module.Dual ℂ V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow a (SymPow b V)))
    (he : ∀ (g : V ≃ₗ[ℂ] V) x y,
      e (plethysmAction b a g.dualMap x) y = e x (plethysmAction b a g y))
    (hf : ∀ (g : V ≃ₗ[ℂ] V) x y,
      f (plethysmAction a b g.dualMap x) y = f x (plethysmAction a b g y))
    (hsurj : ∃ μ : SymPow b (SymPow a (Module.Dual ℂ V)) →ₗ[ℂ]
      SymPow a (SymPow b (Module.Dual ℂ V)),
      IsFoulkesMap a b (Module.Dual ℂ V) μ ∧ Function.Surjective μ) :
    ∃ ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V),
      IsGLEquivariantEmbedding a b V ι := by
  obtain ⟨μ, hformula, hsurj⟩ := hsurj
  exact exists_embedding_of_dual_surjection a b e f he hf μ hsurj
    (fun g => (hformula.commutes g.dualMap).symm)

end PlethysmDual
end Problem346

end

end OAI
