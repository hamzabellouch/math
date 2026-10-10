import OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponent.CurveZeroPole
open PiExponentSeshadri.Geometry

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

local instance : HasExt.{1} (parameterCurve f hf).Modules := HasExt.standard _

private def parameterCurveUnit : (parameterCurve f hf).Modules :=
  SheafOfModules.unit (parameterCurve f hf).ringCatSheaf

instance parameterCurve_isSeparated : (parameterCurve f hf).IsSeparated := by
  rw [Scheme.isSeparated_iff]
  rw [← terminal.comp_from (parameterCurveStructureMap f hf)]
  infer_instance

def parameterCurveAffineOpens (i : Fin 2) : (parameterCurve f hf).Opens :=
  if i = 0 then (zeroChartInclusion f hf).opensRange
  else (infinityChartInclusion f hf).opensRange

omit [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E] in
theorem parameterCurveAffineOpens_affine (i : Fin 2) :
    IsAffineOpen (parameterCurveAffineOpens f hf i) := by
  unfold parameterCurveAffineOpens
  split <;> exact isAffineOpen_opensRange _

omit [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E] in
theorem parameterCurveAffineOpens_cover :
    (⨆ i, parameterCurveAffineOpens f hf i) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨0, by simp [parameterCurveAffineOpens, Scheme.Hom.mem_opensRange]⟩
  · apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨1, by simp [parameterCurveAffineOpens, Scheme.Hom.mem_opensRange]⟩

theorem parameterCurve_ext_zero
    (M : (parameterCurve f hf).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : 2 ≤ q)
    (x : Ext.{1} (C := (parameterCurve f hf).Modules)
      (parameterCurveUnit f hf) M q) : x = 0 := by
  exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover 2 (by omega)
    (parameterCurveAffineOpens f hf) (parameterCurveAffineOpens_affine f hf)
    (parameterCurveAffineOpens_cover f hf) M q hq x

theorem parameterCurve_lineBundle_ext_zero
    (L : LineBundle (parameterCurve f hf)) (q : ℕ) (hq : 2 ≤ q)
    (x : Ext.{1} (C := (parameterCurve f hf).Modules)
      (parameterCurveUnit f hf) L.sheaf q) :
    x = 0 := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  let : L.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose.isQuasicoherent
  exact parameterCurve_ext_zero f hf L.sheaf q hq x

end PiExponent.CurveNormalizationModel

end

end OAI
