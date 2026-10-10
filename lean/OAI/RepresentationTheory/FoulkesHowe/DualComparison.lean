import OAI.RepresentationTheory.FoulkesHowe.DualEquivalence
import OAI.RepresentationTheory.FoulkesHowe.PlethysmDual

namespace OAI

noncomputable section
namespace Problem346

/-- The canonical symmetric-power pairing is natural for arbitrary linear maps. -/
theorem canonicalSymPowDualMap_adjoint (n : ℕ) {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] W) (p : SymPow n (Module.Dual ℂ W)) (q : SymPow n V) :
    symPowDualMap n V (symPowMap n A.dualMap p) q =
      symPowDualMap n W p (symPowMap n A q) := by
  have h : (symPowDualMap n V).comp (symPowMap n A.dualMap) =
      (symPowMap n A).dualMap.comp (symPowDualMap n W) := by
    apply symPow_linearMap_ext n (Module.Dual ℂ W)
    intro φ
    apply symPow_linearMap_ext n V
    intro x
    simp only [LinearMap.comp_apply, LinearMap.dualMap_apply,
      symPowMap_symMonomial, symPowDualMap_monomial]
    rfl
  exact congrArg (fun f : Module.Dual ℂ (SymPow n V) => f q)
    (LinearMap.congr_fun h p)

/-- The perfect-pairing equivalence has the same adjointness identity. -/
theorem canonicalSymPowDualEquiv_adjoint (n : ℕ) {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) (p : SymPow n (Module.Dual ℂ W)) (q : SymPow n V) :
    symPowDualEquiv n V (symPowMap n A.dualMap p) q =
      symPowDualEquiv n W p (symPowMap n A q) :=
  canonicalSymPowDualMap_adjoint n A p q

/-- Canonical duality on a nested symmetric power. -/
def concretePlethysmDualEquiv (outer inner : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    SymPow outer (SymPow inner (Module.Dual ℂ V)) ≃ₗ[ℂ]
      Module.Dual ℂ (SymPow outer (SymPow inner V)) :=
  PlethysmDual.plethysmDualEquivOf outer inner
    (symPowDualEquiv inner V) (symPowDualEquiv outer (SymPow inner V))

theorem concretePlethysmDualEquiv_adjoint (outer inner : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (g : V ≃ₗ[ℂ] V)
    (p : SymPow outer (SymPow inner (Module.Dual ℂ V)))
    (q : SymPow outer (SymPow inner V)) :
    concretePlethysmDualEquiv outer inner V
      (plethysmAction outer inner g.dualMap p) q =
      concretePlethysmDualEquiv outer inner V p (plethysmAction outer inner g q) := by
  apply PlethysmDual.plethysmDualEquivOf_adjoint
  · intro x y
    exact canonicalSymPowDualEquiv_adjoint inner g.toLinearMap x y
  · intro x y
    exact canonicalSymPowDualEquiv_adjoint outer (symPowMap inner g.toLinearMap) x y

/-- A canonical surjection at the dual vector space supplies the required
GL-equivariant comparison embedding, using the concrete perfect pairings. -/
theorem comparison_embedding_of_dual_foulkes_surjection (a b : ℕ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hsurj : ∃ μ : SymPow b (SymPow a (Module.Dual ℂ V)) →ₗ[ℂ]
      SymPow a (SymPow b (Module.Dual ℂ V)),
      IsFoulkesMap a b (Module.Dual ℂ V) μ ∧ Function.Surjective μ) :
    ∃ ι : SymPow a (SymPow b V) →ₗ[ℂ] SymPow b (SymPow a V),
      IsGLEquivariantEmbedding a b V ι :=
  PlethysmDual.comparison_of_dual_charts a b
    (concretePlethysmDualEquiv b a V) (concretePlethysmDualEquiv a b V)
    (concretePlethysmDualEquiv_adjoint b a V)
    (concretePlethysmDualEquiv_adjoint a b V) hsurj

end Problem346

end

end OAI
