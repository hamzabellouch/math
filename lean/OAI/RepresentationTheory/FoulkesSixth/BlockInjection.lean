import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.QuadraticInjection
import OAI.RepresentationTheory.FoulkesSixth.BlockVanishing

namespace OAI

noncomputable section

namespace Foulkes.Canonical
universe u
open Module MvPolynomial SymmetricTensor Polarization
variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable {n : ℕ} (B : Basis (Fin n) ℂ V) (a b : ℕ)
theorem productPolynomial_range_block (ha : 1 ≤ a) (hb : (a-1)^2 ≤ b) :
    (productPolynomial B a b).range = R a n b := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact productPolynomial_mem B a b x
  · intro p hp
    by_contra hnot
    obtain ⟨l, hlp, hlrange⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill (f : P a n) (hf : f ∈ (productPolynomial B a b).range) : l f = 0 := by
      have hh : l f ∈ ((productPolynomial B a b).range).map l := Submodule.mem_map.mpr ⟨f,hf,rfl⟩
      rwa [hlrange, Submodule.mem_bot] at hh
    let lav := l.comp (Polarization.average a n)
    have hs : Vanishing.Symmetric lav := by
      intro σ f
      change l (Polarization.average a n (renameRow σ f)) = l (Polarization.average a n f)
      rw [Vanishing.average_renameRow]
    have hz : Vanishing.ProductsVanish lav b := by
      intro y
      change l (Polarization.average a n (∏ j, z (y j))) = 0
      rw [Polarization.average_eq (show (∏ j, z (a := a) (y j)) ∈ rowInvariants a n from by
        intro σ; simp)]
      exact hkill _ (products_in_range B a b y)
    have hh := Vanishing.block_vanishing a ha hb hs hz p hp.1
    change l (Polarization.average a n p) = 0 at hh
    rw [Polarization.average_eq hp.2] at hh
    exact hlp hh

theorem surjective_block (ha : 1 ≤ a) (hb : (a-1)^2 ≤ b) :
    Function.Surjective (map B a b) := by
  intro x
  have hp : Rows.invariantMap B a b x ∈ (productPolynomial B a b).range := by
    rw [productPolynomial_range_block B a b ha hb]
    exact (Rows.equiv B a b x).property
  obtain ⟨y, hy⟩ := hp
  refine ⟨y, (Rows.invariantMap_injective B a b) ?_⟩
  rw [map_polynomial, hy]

end Foulkes.Canonical

namespace Foulkes.Injection
universe u
open Module
variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

lemma injective_block (ha : 1 ≤ a) (hb : (a-1)^2 ≤ b) :
    Function.Injective (map a b V) :=
  (PlethDual.flipEquiv b a V).symm.injective.comp
    ((LinearMap.dualMap_injective_of_surjective
      (Canonical.surjective_block (Module.finBasis ℂ (Dual ℂ V)) a b ha hb)).comp
      (PlethDual.flipEquiv a b V).injective)

theorem sixth_from_25 (b : ℕ) (hb : 25 ≤ b)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    ∃ i : Sym 6 (Sym b V) →ₗ[ℂ] Sym b (Sym 6 V), Function.Injective i ∧
      ∀ (g : V ≃ₗ[ℂ] V) (x : Sym 6 (Sym b V)),
        i (symMap 6 (symMap b g.toLinearMap) x) = symMap b (symMap 6 g.toLinearMap) (i x) :=
  ⟨map 6 b V, injective_block 6 b V (by omega) (by simpa using hb),
    fun g x => natural 6 b V g.toLinearMap x⟩

end Foulkes.Injection

end

end OAI
