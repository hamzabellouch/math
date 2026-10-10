import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegerPeriodicity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExtendedMultiplier

namespace OAI

/-! The reconstructed arithmetic theta section has the actual Gamma_2
multiplier. Its integer invariance follows from S,T generation. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaNormalizedStabilizer : Subgroup SL(2,Eisenstein) where
  carrier := {g | ∀ p : CubicThetaPoint,
    cubicThetaNormalizedSeriesSection.val (g • p)=cubicThetaNormalizedSeriesSection.val p}
  one_mem' := by intro p; rw [one_smul]
  mul_mem' := by intro g h hg hh p; rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg p
    have he := hg (g⁻¹ • p)
    rw [smul_inv_smul] at he
    exact he.symm

lemma cubicThetaNormalizedSeries_modularT (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaModularT • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  have hm : cubicThetaModularT=cubicThetaFullTranslation 1 := by
    apply Subtype.ext
    rfl
  have hp : (cubicThetaModularT • p).val=(p.val.1+1,p.val.2) := by
    rw [hm,cubicThetaFullPointAction_apply,cubicThetaFullTranslation_complex,
      cubicThetaMobius_translation]
    simp only [Subalgebra.coe_one]
  have hpoint : cubicThetaModularT • p=(⟨(p.val.1+1,p.val.2),p.property⟩ : CubicThetaPoint) :=
    Subtype.ext hp
  rw [hpoint]
  exact cubicThetaNormalizedSeries_integer_periodic p.property

theorem cubicThetaNormalizedSeries_integer (u : SL(2,ℤ)) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaIntegerEmbedding u • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  have hgen : Subgroup.closure {ModularGroup.S,ModularGroup.T} ≤
      cubicThetaNormalizedStabilizer.comap cubicThetaIntegerEmbedding := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · change ∀ p : CubicThetaPoint,
        cubicThetaNormalizedSeriesSection.val (cubicThetaIntegerEmbedding ModularGroup.S • p)=_
      rw [cubicThetaIntegerEmbedding_S]
      exact cubicThetaNormalizedSeriesSection_inversion
    · have haT := Set.mem_singleton_iff.mp ha
      subst a
      change ∀ p : CubicThetaPoint,
        cubicThetaNormalizedSeriesSection.val (cubicThetaIntegerEmbedding ModularGroup.T • p)=_
      rw [cubicThetaIntegerEmbedding_T]
      exact cubicThetaNormalizedSeries_modularT
  have hu : u∈Subgroup.closure {ModularGroup.S,ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  exact hgen hu p

theorem cubicThetaNormalizedSeries_extended (g : cubicThetaExtendedGroup) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g.val • p)=
      cubicThetaExtendedValue g*cubicThetaNormalizedSeriesSection.val p := by
  rw [cubicThetaExtended_decomposition g,mul_smul]
  change cubicThetaNormalizedSeriesSection.val
    (cubicThetaExtendedPrincipal g • (cubicThetaIntegerEmbedding (cubicThetaExtendedInteger g) • p))=_
  rw [cubicThetaNormalizedSeriesSection.property,cubicThetaNormalizedSeries_integer]
  rfl

end CubicFirstMoment

end

end OAI
