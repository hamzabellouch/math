import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1Trace
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeAtkinPairing

namespace OAI

/-! Covariance of actual gradient pairings and the Atkin adjoint identity
on the finite cubed-prime cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1_covariance (F : cubicThetaPointC1)
    (g : cubicThetaPrincipalGroup)
    (hF : ∀ x,F.val (g • x)=cubicThetaKubotaValue g*F.val x) :
    cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) F=cubicThetaKubotaValue g • F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact hF

lemma cubicThetaPointC1Pair_covariance (F G : cubicThetaPointC1)
    (g : cubicThetaPrincipalGroup)
    (hF : ∀ x,F.val (g • x)=cubicThetaKubotaValue g*F.val x)
    (hG : ∀ x,G.val (g • x)=cubicThetaKubotaValue g*G.val x)
    (x : CubicThetaPoint) :
    inner ℂ (cubicThetaPointC1Gradient (g • x) G) (cubicThetaPointC1Gradient (g • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x G) (cubicThetaPointC1Gradient x F) := by
  have he := cubicThetaPointC1Pullback_gradient_pair (cubicThetaPrincipalComplex g) G F x
  rw [cubicThetaPointC1_covariance G g hG,cubicThetaPointC1_covariance F g hF,
    map_smul,map_smul,inner_smul_left,inner_smul_right] at he
  have hk : (starRingEnd ℂ) (cubicThetaKubotaValue g)*cubicThetaKubotaValue g=1 := by
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,cubicThetaKubotaValue_norm]
    norm_num
  rw [←mul_assoc,hk,one_mul] at he
  exact he.symm

lemma cubicThetaPointC1Atkin_covariance {p : Eisenstein} (hp : primaryPrime p)
    (G : cubicThetaPointC1)
    (hG : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,
      G.val (g.val • x)=cubicThetaKubotaValue g.val*G.val x)
    (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
    (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) G).val (g.val • x)=
      cubicThetaKubotaValue g.val*(cubicThetaPointC1Pullback
        (cubicThetaPrimeCubeAtkinMatrix hp) G).val x := by
  change G.val (cubicThetaPrimeCubeAtkinMatrix hp • (g • x))=
    cubicThetaKubotaValue g.val*G.val (cubicThetaPrimeCubeAtkinMatrix hp • x)
  rw [cubicThetaPrimeCubeAtkinPoint_intertwines]
  change G.val ((cubicThetaPrimeCubeAtkinConjugate hp g).val •
    (cubicThetaPrimeCubeAtkinMatrix hp • x))=_
  rw [hG,cubicThetaPrimeCubeAtkinConjugate_kubota]

theorem cubicThetaPointC1Atkin_gradient_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPointC1)
    (hF : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,
      F.val (g.val • x)=cubicThetaKubotaValue g.val*F.val x)
    (hG : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,
      G.val (g.val • x)=cubicThetaKubotaValue g.val*G.val x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) F))
      ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) G))
        (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure := by
  let W := cubicThetaPrimeCubeAtkinMatrix hp
  have hi (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (g • x) (cubicThetaPointC1Pullback W G))
        (cubicThetaPointC1Gradient (g • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback W G))
        (cubicThetaPointC1Gradient x F) :=
    cubicThetaPointC1Pair_covariance F (cubicThetaPointC1Pullback W G) g.val (hF g)
      (cubicThetaPointC1Atkin_covariance hp G hG g) x
  have he := cubicThetaPrimeCubeComplexAtkin_integral hp
    (f:=fun x => inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback W G))
      (cubicThetaPointC1Gradient x F)) hi
  have hGG : cubicThetaPointC1Pullback W (cubicThetaPointC1Pullback W G)=G := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg G.val (cubicThetaPrimeCubeAtkinPoint_involutive hp x)
  have ht (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (W • x) (cubicThetaPointC1Pullback W G))
        (cubicThetaPointC1Gradient (W • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback W F)) := by
    rw [←cubicThetaPointC1Pullback_gradient_pair W,hGG]
  dsimp [W] at he ht
  simpa only [ht] using he

end CubicFirstMoment

end

end OAI
