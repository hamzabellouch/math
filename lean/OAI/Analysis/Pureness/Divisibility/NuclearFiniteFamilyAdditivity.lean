import OAI.Analysis.Pureness.Tensor.FiniteMatrixNuclearity
import OAI.Analysis.Pureness.States.FiniteFamilyAmplification
import OAI.Analysis.Pureness.States.FiniteFamilyMatrixRank

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem CompatibleFiniteQuasitrace.level_additive_of_nuclear
    (F : CompatibleFiniteQuasitrace A) (hsimple : TopologicallySimple A)
    (hA : IsNuclear.{u,0} A)
    (hmono : ∀ k, Monotone (fun a : Positive (FinMatrix A k) => (F.level k a.1).re))
    (hF : F.level 1 1=1) (n : ℕ) :
    ∀ M N : FinMatrix A n, F.level n (M+N)=F.level n M+F.level n N := by
  cases n with
  | zero =>
    intro M N
    have hM : M=0 := by ext i; exact Fin.elim0 i
    have hN : N=0 := by ext i; exact Fin.elim0 i
    simp only [hM,hN,add_zero,(F.level 0).map_zero]
  | succ n =>
    exact F.level_additive_of_matrix_nuclear hsimple hmono hF (n+1) (by omega)
      (hA.finMatrix (n+1) (by omega))

variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

include hA in
theorem normalizedRegularizedStateFiniteFamily_additive (n : ℕ) :
    ∀ M N : FinMatrix A n,
      (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n (M+N)=
        (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n M+
        (normalizedRegularizedStateFiniteFamily hsimple y hy f).level n N :=
  (normalizedRegularizedStateFiniteFamily hsimple y hy f).level_additive_of_nuclear hsimple hA
    (normalizedRegularizedStateFiniteFamily_monotone hsimple y hy f)
    (normalizedRegularizedStateFiniteFamily_unit hsimple y hy f) n

theorem nuclearRegularizedStateTrace_matrix_value (n : ℕ) (M : Positive (FinMatrix A n)) :
    sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)
      (Positive.map (matrixLimitStage n) M)=
      ENNReal.ofReal (((normalizedRegularizedStateFiniteFamily hsimple y hy f).level n M.1).re) :=
  nuclearRegularizedStateTrace_matrix_value_of_additive hsimple hA y hy f n
    (normalizedRegularizedStateFiniteFamily_additive hsimple hA y hy f n) M

theorem nuclearRegularizedStateTrace_matrix_rank (n : ℕ) (M : Positive (FinMatrix A n)) :
    (sharedExtendedTrace (nuclearRegularizedStateTrace hsimple hA y hy f)).rank
      (Positive.map (matrixLimitStage n) M)=
      (ENNReal.ofReal (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹)*
        regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n M) :=
  nuclearRegularizedStateTrace_matrix_rank_of_additive hsimple hA y hy f n
    (normalizedRegularizedStateFiniteFamily_additive hsimple hA y hy f n) M
end CuntzPureness

end

end OAI
