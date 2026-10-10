import OAI.NumberTheory.PiExponent.Cohomology.CechOne
import OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveTwistCech

namespace OAI

namespace PiExponent.ProjectiveTwistAcyclicity

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport.CechOne
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

private abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

private abbrev schemeUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

structure LaurentChartPresentation (U : ι → X.Opens) (M : X.Modules) (d : ℤ) where
  vertex : ∀ i, (schemeFreeOpen (U i) ⟶ M) →+ Laurent ι K d
  vertex_regular : ∀ i b, RegularOn {i} (vertex i b)
  vertex_surjective : ∀ i p, RegularOn {i} p → ∃ b, vertex i b = p
  pair : ∀ i j, (schemeFreeOpen (U i ⊓ U j) ⟶ M) →+ Laurent ι K d
  pair_injective : ∀ i j, Function.Injective (pair i j)
  pair_regular : ∀ i j c, RegularOn {i, j} (pair i j c)
  pair_left : ∀ i j b, pair i j (restrictHom X.ringCatSheaf inf_le_left b) = vertex i b
  pair_right : ∀ i j b, pair i j (restrictHom X.ringCatSheaf inf_le_right b) = vertex j b
  triple : ∀ i j k, (schemeFreeOpen ((U i ⊓ U j) ⊓ U k) ⟶ M) →+ Laurent ι K d
  triple_first : ∀ i j k c, triple i j k
      (restrictHom X.ringCatSheaf inf_le_left c) = pair i j c
  triple_second : ∀ i j k c, triple i j k
      (restrictHom X.ringCatSheaf
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) c) = pair j k c
  triple_outer : ∀ i j k c, triple i j k
      (restrictHom X.ringCatSheaf
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) c) = pair i k c

theorem hasPrimitives_of_laurent_charts {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
    (hd : 0 ≤ d) (P : LaurentChartPresentation (K := K) U M d) :
    HasPrimitives X.ringCatSheaf U M := by
  intro c hc
  let C (i j : ι) : Laurent ι K d := P.pair i j (c i j)
  have hregular : ∀ i j, RegularOn {i, j} (C i j) := fun i j => P.pair_regular i j _
  have hcoc : ∀ i j k, C i j + C j k = C i k := by
    intro i j k
    have h := congrArg (P.triple i j k) (hc i j k)
    erw [map_add] at h
    simpa only [P.triple_first, P.triple_second, P.triple_outer] using h
  obtain ⟨B, hB, hCB⟩ := nonnegative_twist_cech_exact hd C hregular hcoc
  choose b hb using fun i => P.vertex_surjective i (B i) (hB i)
  refine ⟨b, fun i j => ?_⟩
  apply P.pair_injective i j
  erw [map_sub, P.pair_right, P.pair_left, hb j, hb i]
  exact hCB i j

theorem ext_one_eq_zero_of_laurent_charts [IsNoetherian X]
    {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (d : ℤ) (hd : 0 ≤ d)
    (P : LaurentChartPresentation (K := K) U M d)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit (X := X)) M 1) : x = 0 := by
  let e : schemeFreeOpen (X := X) ⊤ ≅ schemeUnit (X := X) :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen ⊤) M 1, z = 0 := by
    apply ext_one_eq_zero_of_primitives X.ringCatSheaf U ⊤ (fun _ => le_top)
      (by rw [hcover]) M
    · intro i z
      exact PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero (U i) (hU i) M 0 z
    · exact hasPrimitives_of_laurent_charts hd P
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add 1))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

theorem ext_succ_eq_zero_of_laurent_cech_charts [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (d : ℤ) (hd : 0 ≤ d)
    (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
    (q : ℕ) (x : Ext.{u+1} (C := X.Modules) (schemeUnit (X := X)) M (q + 1)) : x = 0 := by
  let e : schemeFreeOpen (X := X) ⊤ ≅ schemeUnit (X := X) :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen ⊤) M (q + 1), z = 0 := by
    apply GeometrySupport.CechHigher.affine_ext_succ_eq_zero_of_injective_cech
      X M U ⊤ (fun _ => le_top) (by rw [hcover])
    · intro n t
      exact IsAffineOpen.iInf (fun i => hU (t i))
    · intro I hI n
      exact @GeometrySupport.FreeCechSections.injective_hasPrimitives _ _ U X.ringCatSheaf I hI n
    · exact P.hasPrimitives hd q
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (q + 1)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add (q + 1))))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end
end PiExponent.ProjectiveTwistAcyclicity

end OAI
