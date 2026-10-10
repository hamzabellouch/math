import OAI.Algebra.AuslanderReiten.Ext.ExtBridge
import OAI.Algebra.AuslanderReiten.Complete.CompleteComparison
import OAI.Algebra.AuslanderReiten.Stable.StableHom

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ}
variable {N : Type u} [AddCommGroup N] [Module R N]

def completeExtCocycleMap (n : ℤ) (f : P.X n →ₗ[R] N)
    (hf : f.comp (P.d (n + 1) n).hom = 0) : Cokernel P n →ₗ[R] N :=
  (LinearMap.range (P.d (n + 1) n).hom).liftQ f (LinearMap.range_le_ker_iff.mpr hf)

@[simp] theorem completeExtCocycleMap_mk (n : ℤ) (f : P.X n →ₗ[R] N)
    (hf : f.comp (P.d (n + 1) n).hom = 0) (x : P.X n) :
    completeExtCocycleMap n f hf ((LinearMap.range (P.d (n + 1) n).hom).mkQ x) = f x := rfl

theorem completeExtCocycleMap_stable_zero_iff (hP : TotallyAcyclicComplex P)
    (n : ℤ) (f : P.X n →ₗ[R] N) (hf : f.comp (P.d (n + 1) n).hom = 0) :
    StableHom.classOf R _ N (completeExtCocycleMap n f hf) = 0 ↔
      ∃ g : P.X (n - 1) →ₗ[R] N, g.comp (P.d n (n - 1)).hom = f := by
  rw [StableHom.classOf_eq_zero_iff_projective]
  constructor
  · rintro ⟨Q, hQ, hRQ, hproj, hfin, i, p, hip⟩
    let π := (LinearMap.range (P.d (n + 1) n).hom).mkQ
    have hi : (i.comp π).comp (P.d (n + 1) n).hom = 0 := by
      rw [LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
    obtain ⟨g, hg⟩ := (hP.dualExact n).projective (i.comp π) hi
    refine ⟨p.comp g, ?_⟩
    rw [LinearMap.comp_assoc, hg, ← LinearMap.comp_assoc, hip]
    rfl
  · rintro ⟨g, hg⟩
    let := hP.finite (n - 1)
    let := hP.projective (n - 1)
    let d : Cokernel P n →ₗ[R] P.X (n - 1) :=
      completeExtCocycleMap n (P.d n (n - 1)).hom (differential_comp P _ _ _)
    refine ⟨P.X (n - 1), inferInstance, inferInstance, inferInstance, inferInstance, d, g, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
    exact DFunLike.congr_fun hg x

theorem positiveExtVanish_of_stableCokernels (hP : TotallyAcyclicComplex P)
    (h : ∀ n : ℕ, Subsingleton (StableHom R (Cokernel P ((n + 1 : ℕ) : ℤ)) N)) :
    PositiveExtVanish R (Cokernel P 0) N := by
  apply (positiveExtVanish_iff_completeResolution R (Cokernel P 0) N P
    hP.projective hP.exactAt (LinearEquiv.refl R _)).mpr
  intro n f hf
  have hi : ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) := by omega
  have hf' : f.comp (P.d (((n + 1 : ℕ) : ℤ) + 1) ((n + 1 : ℕ) : ℤ)).hom = 0 := by
    rw [hi]
    exact hf
  have := h n
  have hz : StableHom.classOf R _ N (completeExtCocycleMap ((n + 1 : ℕ) : ℤ) f hf') = 0 :=
    Subsingleton.elim _ _
  have hgex := (completeExtCocycleMap_stable_zero_iff hP _ f hf').mp hz
  have hn : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [hn] at hgex
  obtain ⟨g, hg⟩ := hgex
  exact ⟨g, hg.symm⟩

end ArExplicit

end

end OAI
