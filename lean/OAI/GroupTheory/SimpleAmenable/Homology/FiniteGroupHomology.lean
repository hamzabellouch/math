import Mathlib

namespace OAI

section
open CategoryTheory Limits
namespace FiniteGroupHomology
universe u
variable {R G : Type u} [CommRing R] [IsNoetherianRing R] [Group G]
lemma of_finite_chains (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [Module.Finite R (K.X n)] : Module.Finite R (K.homology n) := by
  have : Module.Finite R (K.cycles n) :=
    Module.Finite.of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ n).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

lemma finite (A : Rep R G) [Finite G] [Module.Finite R A] (n : ℕ) :
    Module.Finite R (groupHomology A n) := by
  change Module.Finite R ((groupHomology.inhomogeneousChains A).homology n)
  apply of_finite_chains
end FiniteGroupHomology

end

section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
open scoped _root_.CategoryTheory _root_.CategoryTheory.Functor
variable {C : Type*} [Category* C]

lemma isEventuallyConstantFrom_of_succ (F : ℕ ⥤ C) (N : ℕ)
    (h : ∀ n, N ≤ n → _root_.CategoryTheory.IsIso (F.map (_root_.CategoryTheory.homOfLE (Nat.le_succ n)))) :
    F.IsEventuallyConstantFrom N := by
  intro n f
  have hn : N ≤ n := _root_.CategoryTheory.leOfHom f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero =>
      have hf : f = 𝟙 N := Subsingleton.elim _ _
      rw [hf, F.map_id]
      infer_instance
  | succ k ih =>
      have : _root_.CategoryTheory.IsIso (F.map (_root_.CategoryTheory.homOfLE (show N ≤ N+k by omega))) := ih _ (by omega)
      have := h (N+k) (by omega)
      have hf : f = (_root_.CategoryTheory.homOfLE (show N ≤ N+k by omega)) ≫
          (_root_.CategoryTheory.homOfLE (Nat.le_succ (N+k))) := Subsingleton.elim _ _
      rw [hf, F.map_comp]
      infer_instance
end CategoryTheory.Functor

namespace FixedStageReturn

lemma stage_ι_isIso {R : Type*} [Ring R] (F : ℕ ⥤ ModuleCat R) (N m : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) (hm : N ≤ m) :
    IsIso (colimit.ι F m) := by
  exact (_root_.OAI.CategoryTheory.Functor.isEventuallyConstantFrom_of_succ F N h).isIso_ι_of_isColimit'
    (colimit.isColimit F) m (homOfLE hm)

lemma finite_stage_iff_colimit {R : Type*} [Ring R] (F : ℕ ⥤ ModuleCat R) (N m : ℕ)
    (h : ∀ n, N ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)))) (hm : N ≤ m) :
    Module.Finite R (F.obj m) ↔ Module.Finite R (colimit F : ModuleCat R) := by
  have := stage_ι_isIso F N m h hm
  constructor
  · intro hfin
    exact Module.Finite.of_surjective (colimit.ι F m).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  · intro hfin
    exact Module.Finite.of_surjective (inv (colimit.ι F m)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end FixedStageReturn

end

end OAI
