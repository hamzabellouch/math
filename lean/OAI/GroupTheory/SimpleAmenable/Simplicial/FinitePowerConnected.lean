import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ConstantSplit
import OAI.GroupTheory.SimpleAmenable.Simplicial.FinitePowerLow

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open FreeChains

attribute [local instance 1200] Pi.module Prod.instModule

def LowConnected (X:SSet) : Prop := ∀ j:ℕ, 0 < j → j < 3 → IsZero (X.homology Z j)
namespace LowConnected
variable {X Y:SSet}
lemma of_iso (e:X≅Y) (h:LowConnected Y) : LowConnected X :=
  fun j hj h3 => IsZero.of_iso (h j hj h3) ((SSet.homologyFunctor Z j).mapIso e)
lemma one : LowConnected ConnectedProduct.one := fun j hj _ =>
  ConnectedProduct.one_homology_zero j (by omega)
lemma projection_isIso [X.IsConnected] [Y.IsConnected] (hX:LowConnected X) (hY:LowConnected Y)
    (j:ℕ) (hj:0<j) (hj5:j≤5) : IsIso (ConnectedProduct.projection X Y j) := by
  apply ConnectedProduct.projection_isIso_arbitrary X Y 3 3 j hj (by omega)
  · intro i hi h3; exact homology_isZero_complex X i (hX i hi h3)
  · intro i hi h3; exact homology_isZero_complex Y i (hY i hi h3)
lemma tensor [X.IsConnected] [Y.IsConnected] (hX:LowConnected X) (hY:LowConnected Y) :
    LowConnected (X⊗Y) := by
  intro j hj h3
  have := projection_isIso hX hY j hj (by omega)
  exact IsZero.of_iso ((biprod_isZero_iff _ _).mpr ⟨hX j hj h3,hY j hj h3⟩)
    (asIso (ConnectedProduct.projection X Y j))
lemma fin [X.IsConnected] (hX:LowConnected X) (s:ℕ) : LowConnected ((power (Fin s)).obj X) := by
  induction s with
  | zero => exact of_iso (finZeroIso X) one
  | succ s ih => exact of_iso (finSuccIso X s) (tensor hX ih)
lemma power [X.IsConnected] (hX:LowConnected X) (κ:Type) [Finite κ] : LowConnected ((BarFinitePower.power κ).obj X) := by
  let := Fintype.ofFinite κ
  exact of_iso (reindexIso X (Fintype.equivFin κ)) (fin hX _)
end LowConnected
variable (X:SSet) [X.IsConnected] (hX:LowConnected X)
include hX in
lemma coordinates_fin_isIso_connected (s j:ℕ) (hj:0<j) (hj5:j≤5) :
    IsIso (coordinates (Fin s) X j) := by
  induction s with
  | zero =>
    have hz : IsZero (((power (Fin 0)).obj X).homology Z j) :=
      IsZero.of_iso (ConnectedProduct.one_homology_zero j (by omega))
        ((SSet.homologyFunctor Z j).mapIso (finZeroIso X))
    exact hz.isIso (ModuleCat.isZero_iff_subsingleton.mpr inferInstance) _
  | succ s ih =>
    have := ih
    have := LowConnected.projection_isIso hX (hX.fin s) j hj hj5
    have : IsIso (biprod.map (𝟙 (X.homology Z j)) (coordinates (Fin s) X j)) := by
      change IsIso (biprod.mapIso (Iso.refl _) (asIso (coordinates (Fin s) X j))).hom
      infer_instance
    have : IsIso (coordinates (Fin (s+1)) X j ≫ (coordinateSplit (X.homology Z j) s).hom) := by
      rw [coordinates_fin_succ]; infer_instance
    exact (isIso_comp_right_iff _ (coordinateSplit (X.homology Z j) s).hom).mp inferInstance
include hX in
lemma coordinates_isIso_connected (κ:Type) [Finite κ] (j:ℕ) (hj:0<j) (hj5:j≤5) :
    IsIso (coordinates κ X j) := by
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  have := coordinates_fin_isIso_connected X hX (Fintype.card κ) j hj hj5
  have : IsIso (coordinates κ X j ≫ (coefficientReindex e (X.homology Z j)).hom) := by
    rw [coordinates_reindex]; infer_instance
  exact (isIso_comp_right_iff _ (coefficientReindex e (X.homology Z j)).hom).mp inferInstance
end BarFinitePower

end

end

end OAI
