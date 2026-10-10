import OAI.Algebra.Finitistic.Iteration.IntegerIterateAmplitude

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace DerivedBar.IterateSupport
universe u w v
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]
variable {E : Type w} [Category.{v} E] [Abelian E]
variable (F : ModuleCat.{u} D ⥤ E) [F.Additive]
variable (g : ℕ) (hg : ∀ M : ModuleCat.{u} D, HasProjectiveDimensionLE M g)

include hg in
/-- A terminal additive functor applied to the actual projective bar resolution
has finite support when the input has finite cohomological support. This covers
balanced tensor with arbitrary right modules, not just the fixed bimodule. -/
theorem additive_resolved_exact_above (Z : ChainComplex (ModuleCat.{u} D) ℕ) (m : ℕ)
    (hZ : ∀ i, m < i → Z.ExactAt i) (n : ℕ) (hn : m+g+2 < n) :
    ((F.mapHomologicalComplex (.down ℕ)).obj (barTotal k D Z)).ExactAt n := by
  apply ProjectiveTail.map_exact_tail (barTotal k D Z) F (m+1) g
  · intro i hi
    exact (exactAt_iff_of_quasiIsoAt (barTotalAugmentation k D Z) i).mpr (hZ i (by omega))
  · exact barTotal_projective k D Z
  · exact hg
  · omega

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)

include hg in
omit [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k Dᵐᵒᵖ X] in
/-- The extra resolved tensor used for residue/base Tor also has a finite
bound, uniformly after every actual derived iteration. -/
theorem iterated_additive_exact_above (r n : ℕ) (hn : (r+1)*(g+2) < n) :
    ((F.mapHomologicalComplex (.down ℕ)).obj
      (barTotal k D (resolvedModel k D X N r))).ExactAt n := by
  apply additive_resolved_exact_above k D F g hg (resolvedModel k D X N r)
    (r*(g+2)) (resolvedModel_exact_above k D X g hg N r) n
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hn

local instance : HasDerivedCategory.{u+1} (ModuleCat.{u} D) :=
  HasDerivedCategory.standard (ModuleCat.{u} D)

include hg in
/-- Nonzero genuine iterates are detected in a proved finite cohomological window. -/
theorem nonzero_in_finite_window (r : ℕ) (h : ¬ IsZero (object k D X N r)) :
    ∃ n : ℕ, n ≤ r*(g+2) ∧
      ¬ IsZero ((DerivedCategory.homologyFunctor (ModuleCat D) (-(n : ℤ))).obj
        (object k D X N r)) := by
  obtain ⟨n,hn⟩ := nonzero_homology k D X N r h
  refine ⟨n, ?_, hn⟩
  by_contra hbound
  have := isGE_bound k D X g hg N r
  apply hn
  exact DerivedCategory.isZero_of_isGE _ (-((r*(g+2) : ℕ) : ℤ)) (-(n : ℤ)) (by omega)
end DerivedBar.IterateSupport

end

end OAI
