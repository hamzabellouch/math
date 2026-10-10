import OAI.Algebra.AuslanderReiten.Duality.IdealDualComparison
import OAI.Algebra.AuslanderReiten.Homology.DerivedSingle
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q

private def exceptionalShortComplex : ShortComplex (ModuleCat C) :=
  ShortComplex.moduleCatMk (RightDual.map (k := k) (leftEll q q))
    (RightDual.map (k := k) (leftEll q 1)) (by
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (leftEll q q (leftEll q 1 a)) = 0
      have h := LinearMap.congr_fun (exceptional_differential_comp q) a
      change leftEll q q (leftEll q 1 a) = 0 at h
      rw [h, map_zero])

private def exceptionalShortComplexIso :
    (idealDualComplex q).sc' 3 2 1 ≅ exceptionalShortComplex q :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (leftEll q q a) = φ.functional (leftEll q (q ^ 1) a)
      rw [pow_one])
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply RightDual.ext
      apply LinearMap.ext
      intro a
      change φ.functional (leftEll q 1 a) = φ.functional (leftEll q (q ^ 0) a)
      rw [pow_zero])

def idealDual_homology_two_iso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (idealDualComplex q).homology 2 ≅ ModuleCat.of C (Simple q) :=
  (idealDualComplex q).homologyIsoSc' 3 2 1 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (exceptionalShortComplexIso q) ≪≫
    (exceptionalShortComplex q).moduleCatHomologyIso ≪≫
    (exceptionalDualHomologyEquiv q hq hq1).toModuleIso

def idealDualCochain : CochainComplex (ModuleCat C) ℤ :=
  (idealDualComplex q).extend ComplexShape.embeddingDownNat

theorem idealDualCochain_exact (hq : q ≠ 0) (h : NoPositivePowerOne q)
    (i : ℤ) (hi : i ≠ -2) : (idealDualCochain q).ExactAt i := by
  by_cases hh : ∃ n : ℕ, -(n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hh
    exact ((idealDualComplex q).extend_exactAt_iff ComplexShape.embeddingDownNat
      (j := n) (by rfl)).mpr (idealDual_exactAt q hq h n (by omega))
  · exact (idealDualComplex q).extend_exactAt ComplexShape.embeddingDownNat i
      (by intro n hn; exact hh ⟨n, hn⟩)

def idealDualCochain_homology_iso (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    (idealDualCochain q).homology (-2) ≅ ModuleCat.of C (Simple q) :=
  (idealDualComplex q).extendHomologyIso ComplexShape.embeddingDownNat
    (j := 2) (by rfl) ≪≫ idealDual_homology_two_iso q hq hq1

def idealDualDerivedIso [HasDerivedCategory (ModuleCat C)]
    (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    DerivedCategory.Q.obj (idealDualCochain q) ≅
      ((DerivedCategory.singleFunctor (ModuleCat C) 0).obj (ModuleCat.of C (Simple q)))⟦(2 : ℤ)⟧ :=
  derivedSingleIso (idealDualCochain q) (-2) (idealDualCochain_exact q hq h) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat C) (-2)).mapIso
      (idealDualCochain_homology_iso q hq hq1) ≪≫
    (((DerivedCategory.singleFunctors (ModuleCat C)).shiftIso (2 : ℤ) (-2) 0 (by norm_num)).app _).symm

end ArExplicit.Resolution

end

end OAI
