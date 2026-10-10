import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTranslatedCuspStrip
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinCusp
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactHeight

namespace OAI

/-! Horizontal reduction into the exact half-open cusp strip uses the
actual principal translations. It is compatible with every arithmetic
cusp through the proved conjugation in the level-three group. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrincipalTranslation_coordinates (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaPointCoordinates (cubicThetaPrincipalTranslation w • p)=
      ((cubicThetaPointCoordinates p).1+3*(w:ℂ),(cubicThetaPointCoordinates p).2) := by
  change cubicThetaMobius (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) p.val=_
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
  push_cast
  rfl

lemma cubicThetaCuspStrip_reduction {H : ℝ} (p : CubicThetaPoint)
    (hp : H<cubicThetaPointHeight p) :
    ∃ w : Eisenstein, cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip H := by
  let x := cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1
  let n : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let w := coordinatesEquiv n
  refine ⟨w,?_⟩
  constructor
  · rw [cubicThetaPrincipalTranslation_coordinates]
    exact hp
  · intro i
    rw [cubicThetaPrincipalTranslation_coordinates,cubicThetaPeriodCoordinates_translate]
    have h : (cubicThetaPeriodCoordinates (cubicThetaPointCoordinates p).1+
        fun j => ((coordinatesEquiv.symm w) j:ℝ)) i=Int.fract (x i) := by
      simp only [w,LinearEquiv.symm_apply_apply,Pi.add_apply,n,Int.cast_neg]
      rfl
    rw [h]
    exact ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

def cubicThetaCuspNeighborhood (δ : SL(2,Eisenstein)) (H : ℝ) : Set CubicThetaQuotient :=
  cubicThetaQuotientMap '' cubicThetaTranslatedCuspStrip δ H

lemma cubicThetaCuspNeighborhood_measurable (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H) :
    MeasurableSet (cubicThetaCuspNeighborhood δ H) :=
  cubicThetaQuotient_injective_image_measurable (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH)

lemma cubicThetaCuspNeighborhood_mem_of_height (δ : SL(2,Eisenstein)) {H : ℝ}
    (p : CubicThetaPoint) (hp : H<cubicThetaPointHeight p) :
    cubicThetaQuotientMap (δ • p)∈cubicThetaCuspNeighborhood δ H := by
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hp
  let g := cubicThetaPrincipalTranslation w
  let k := cubicThetaPrincipalConjugate δ⁻¹ g
  have hk : k • (δ • p)=δ • (g • p) := by
    change ((δ⁻¹)⁻¹*g.val*δ⁻¹) • (δ • p)=δ • (g.val • p)
    rw [inv_inv,mul_smul,mul_smul,inv_smul_smul]
  refine ⟨δ • (g • p),⟨g • p,hw,rfl⟩,?_⟩
  rw [← hk,cubicThetaQuotient_covering.map_smul]

end CubicFirstMoment

end

end OAI
