import OAI.Algebra.AuslanderReiten.Cones.MappingConeModule
import OAI.Algebra.AuslanderReiten.Complete.CompleteShiftDual
import OAI.Algebra.AuslanderReiten.Complete.FrobeniusGorenstein
import Mathlib.RingTheory.Finiteness.Prod

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

def coneBlockShortComplex (i : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (coneBlock (G.d i (i + 1)).hom (F.d (i + 1) ((i + 1) + 1)).hom
      (φ.f (i + 1)).hom))
    (ModuleCat.ofHom (coneBlock (G.d (i + 1) ((i + 1) + 1)).hom
      (F.d ((i + 1) + 1) (((i + 1) + 1) + 1)).hom (φ.f ((i + 1) + 1)).hom))
    (by
      apply ModuleCat.hom_ext
      apply coneBlock_comp_zero
      · exact congrArg ModuleCat.Hom.hom (G.d_comp_d _ _ _)
      · exact congrArg ModuleCat.Hom.hom (F.d_comp_d _ _ _)
      · exact congrArg ModuleCat.Hom.hom (φ.comm _ _))

def coneShortComplexIso (i : ℤ) :
    (mappingCone φ).sc' i (i + 1) ((i + 1) + 1) ≅ coneBlockShortComplex φ i :=
  ShortComplex.isoMk (coneTermEquiv φ i).toModuleIso
    (coneTermEquiv φ (i + 1)).toModuleIso (coneTermEquiv φ ((i + 1) + 1)).toModuleIso
    (by
      apply ModuleCat.hom_ext
      exact (coneTermEquiv_differential φ i).symm)
    (by
      apply ModuleCat.hom_ext
      exact (coneTermEquiv_differential φ (i + 1)).symm)

private theorem cochain_adjacent_exact {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveCochain K) (i : ℤ) :
    Function.Exact (K.d i (i + 1)).hom (K.d (i + 1) ((i + 1) + 1)).hom := by
  have h := hK.exactAt (i + 1)
  rw [K.exactAt_iff' (i := i) (j := i + 1) (k := (i + 1) + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact LinearMap.exact_iff.mpr h.symm

private theorem cochain_adjacent_dualExact {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : DualExactCochain K) (i : ℤ) :
    HomExactAt (K.d i (i + 1)).hom (K.d (i + 1) ((i + 1) + 1)).hom := by
  have h := hK (i + 1)
  have hi : (i + 1) - 1 = i := by omega
  rw [hi] at h
  exact h

theorem mappingCone_exactProjective
    (hF : ExactProjectiveCochain F) (hG : ExactProjectiveCochain G) :
    ExactProjectiveCochain (mappingCone φ) where
  finite i := by
    let := hG.finite i
    let := hF.finite (i + 1)
    exact Module.Finite.equiv (coneTermEquiv φ i).symm
  projective i := by
    let := hG.projective i
    let := hF.projective (i + 1)
    exact Module.Projective.of_equiv (coneTermEquiv φ i).symm
  exactAt j := by
    obtain ⟨i, rfl⟩ : ∃ i : ℤ, j = i + 1 := ⟨j - 1, by omega⟩
    rw [(mappingCone φ).exactAt_iff' (i := i) (j := i + 1) (k := (i + 1) + 1) (by simp) (by simp)]
    apply ShortComplex.exact_of_iso (coneShortComplexIso φ i).symm
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (LinearMap.exact_iff.mp (coneBlock_exact _ _ _ _ _ _
      (cochain_adjacent_exact hG i) (cochain_adjacent_exact hF (i + 1))
      (congrArg ModuleCat.Hom.hom (φ.comm _ _)))).symm

theorem mappingCone_dualExact (hF : DualExactCochain F) (hG : DualExactCochain G) :
    DualExactCochain (mappingCone φ) := by
  intro j
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : (i + 1) - 1 = i := by omega
  rw [hi]
  apply HomExactAt.of_shortComplex_iso (coneShortComplexIso φ i).symm
  exact coneBlock_homExact _ _ _ _ _ _ (cochain_adjacent_dualExact hG i)
    (cochain_adjacent_dualExact hF (i + 1)) (congrArg ModuleCat.Hom.hom (φ.comm _ _))

theorem mappingCone_totallyAcyclic
    (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) :
    TotallyAcyclicCochain (mappingCone φ) where
  toExactProjectiveCochain := mappingCone_exactProjective φ hF.toExactProjectiveCochain hG.toExactProjectiveCochain
  dualExact := mappingCone_dualExact φ hF.dualExact hG.dualExact

theorem mappingCone_cokernel_gorenstein
    (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) :
    GorensteinProjective R (Cokernel (chainOfCochain (mappingCone φ)) 0) :=
  gorensteinProjective_of_totallyAcyclic _ _ (mappingCone_totallyAcyclic φ hF hG).to_chain
    (LinearEquiv.refl R _)

end ArExplicit

end

end OAI
