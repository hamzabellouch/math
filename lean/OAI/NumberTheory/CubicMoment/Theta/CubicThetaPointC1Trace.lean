import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1Section
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeComplexIntegration

namespace OAI

/-! The gradient trace identity before integration. Its finite sum uses
the same literal representatives and cubic phases as the Hecke trace. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPointC1Trace {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) : cubicThetaPointC1 := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  exact ∑ t : cubicThetaPrimeCubeTransversal p,
    star (cubicThetaKubotaValue t.val) • cubicThetaPointC1Pullback (cubicThetaPrincipalComplex t.val) F

lemma cubicThetaPointC1Trace_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) (x : CubicThetaPoint) :
    (cubicThetaPointC1Trace hp F).val x=
      ∑' t : cubicThetaPrimeCubeTransversal p,star (cubicThetaKubotaValue t.val)*F.val (t.val • x) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  simp only [cubicThetaPointC1Trace,tsum_fintype]
  simp
  rfl

lemma cubicThetaPointC1Trace_gradient_point {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hG : ∀ g : cubicThetaPrincipalGroup,
      cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) G=cubicThetaKubotaValue g • G)
    (x : CubicThetaPoint) :
    inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp F))=
      ∑' t : cubicThetaPrimeCubeTransversal p,
        inner ℂ (cubicThetaPointC1Gradient (t.val • x) G) (cubicThetaPointC1Gradient (t.val • x) F) := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  simp only [cubicThetaPointC1Trace,map_sum,map_smul,inner_sum,tsum_fintype]
  apply Finset.sum_congr rfl
  intro t _
  have he := cubicThetaPointC1Pullback_gradient_pair (cubicThetaPrincipalComplex t.val) G F x
  rw [hG t.val,map_smul,inner_smul_left] at he
  rw [inner_smul_right]
  change (starRingEnd ℂ) (cubicThetaKubotaValue t.val)*
    inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback (cubicThetaPrincipalComplex t.val) F))=
    inner ℂ (cubicThetaPointC1Gradient (cubicThetaPrincipalComplex t.val • x) G)
      (cubicThetaPointC1Gradient (cubicThetaPrincipalComplex t.val • x) F)
  exact he

lemma cubicThetaPointC1Pair_integrable (F G : cubicThetaPointC1) {S : Set CubicThetaPoint}
    (hF : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x F‖^2) S cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x G‖^2) S cubicThetaPointMeasure) :
    IntegrableOn (fun x => inner ℂ (cubicThetaPointC1Gradient x G)
      (cubicThetaPointC1Gradient x F)) S cubicThetaPointMeasure := by
  apply ((hG.add hF).div_const 2).mono'
    (((cubicThetaPointC1Gradient_continuous G).inner
      (cubicThetaPointC1Gradient_continuous F)).aestronglyMeasurable)
  filter_upwards with x
  change ‖inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x F)‖≤
    (‖cubicThetaPointC1Gradient x G‖^2+‖cubicThetaPointC1Gradient x F‖^2)/2
  apply (norm_inner_le_norm _ _).trans
  have hs := sq_nonneg (‖cubicThetaPointC1Gradient x G‖-‖cubicThetaPointC1Gradient x F‖)
  nlinarith

end CubicFirstMoment

end

end OAI
