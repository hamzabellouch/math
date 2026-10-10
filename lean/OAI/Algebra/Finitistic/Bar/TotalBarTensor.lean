import OAI.Algebra.Finitistic.Bar.TotalBarFunctor
import OAI.Algebra.Finitistic.Bimodule.BimoduleDerived
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u
variable (k D : Type u) [Field k] [Ring D] [Algebra k D]

/-- Resolving a quasi-isomorphism gives a quasi-isomorphism between projective complexes. -/
instance barTotalFunctor_map_quasiIso {Z W : ChainComplex (ModuleCat.{u} D) ℕ}
    (f : Z ⟶ W) [QuasiIso f] : QuasiIso ((barTotalFunctor k D).map f) := by
  apply (quasiIso_iff_comp_right (K := barTotal k D Z) (L := barTotal k D W)
    ((barTotalFunctor k D).map f) (barTotalAugmentation k D W)).mp
  erw [(barTotalAugmentationNat k D).naturality f]
  exact inferInstanceAs (QuasiIso (barTotalAugmentation k D Z ≫ f))

/-- Additive functors preserve quasi-isomorphisms between nonnegative projective complexes.
This uses the proved homotopy-equivalence criterion, not a flatness hypothesis. -/
theorem additive_map_quasiIso_of_projective (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D)
    [G.Additive] {P Q : ChainComplex (ModuleCat.{u} D) ℕ}
    [∀ n, Projective (P.X n)] [∀ n, Projective (Q.X n)]
    (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map f) := by
  obtain ⟨e, he⟩ := (ChainComplex.quasiIso_iff_of_projective f).mp inferInstance
  rw [← he]
  exact (G.mapHomotopyEquiv e).quasiIso_hom

variable (X : Type u) [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- Resolve the entire input complex before applying the actual balanced tensor functor. -/
def tensorTotalFunctor : ChainComplex (ModuleCat.{u} D) ℕ ⥤ ChainComplex (ModuleCat.{u} D) ℕ :=
  barTotalFunctor k D ⋙
    (BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The resolved tensor construction preserves all quasi-isomorphisms. -/
instance tensorTotalFunctor_map_quasiIso {Z W : ChainComplex (ModuleCat.{u} D) ℕ}
    (f : Z ⟶ W) [QuasiIso f] : QuasiIso ((tensorTotalFunctor k D X).map f) := by
  let : ∀ n, Projective (((barTotalFunctor k D).obj Z).X n) := barTotal_projective k D Z
  let : ∀ n, Projective (((barTotalFunctor k D).obj W).X n) := barTotal_projective k D W
  exact additive_map_quasiIso_of_projective D (BimoduleTensor.tensorFunctor k D X)
    ((barTotalFunctor k D).map f)

/-- On a projective chain input, tensoring the augmentation is a quasi-isomorphism,
even when X is not flat. This identifies the construction with tensor of that projective model. -/
instance tensorTotalAugmentation_quasiIso (P : ChainComplex (ModuleCat.{u} D) ℕ)
    [∀ n, Projective (P.X n)] :
    QuasiIso (((BimoduleTensor.tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (barTotalAugmentation k D P)) := by
  let : ∀ n, Projective ((barTotal k D P).X n) := barTotal_projective k D P
  exact additive_map_quasiIso_of_projective D (BimoduleTensor.tensorFunctor k D X)
    (barTotalAugmentation k D P)

/-- Repeated resolution and balanced tensor, proceeding from the right as in Section 6.
The identification with the independently signed literal multibar is a separate obligation. -/
def tensorTotalIterate : ℕ → (ChainComplex (ModuleCat.{u} D) ℕ ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
  | 0 => 𝟭 _
  | r+1 => tensorTotalIterate r ⋙ tensorTotalFunctor k D X

instance tensorTotalIterate_map_quasiIso (r : ℕ) {Z W : ChainComplex (ModuleCat.{u} D) ℕ}
    (f : Z ⟶ W) [QuasiIso f] : QuasiIso ((tensorTotalIterate k D X r).map f) := by
  induction r with
  | zero => exact inferInstanceAs (QuasiIso f)
  | succ r ih =>
    let := ih
    exact tensorTotalFunctor_map_quasiIso k D X ((tensorTotalIterate k D X r).map f)
end DerivedBar

end

end OAI
