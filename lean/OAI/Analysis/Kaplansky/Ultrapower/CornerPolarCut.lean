import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.ApproxPolar

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

open scoped CStarAlgebra in
lemma map_cfc_sqrt (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a) :
    φ (CFC.sqrt a)=CFC.sqrt (φ a) := by
  rw [← cfc_sqrt_real a ha,φ.map_cfc Real.sqrt a (ha:=ha.isSelfAdjoint)
    (hφa:=(map_nonneg φ ha).isSelfAdjoint),cfc_sqrt_real (φ a) (map_nonneg φ ha)]

open scoped CStarAlgebra in
lemma map_polarCut (φ : A →⋆ₐ[ℂ] B) (x : A) {r : ℝ} (hr : 0 < r) :
    φ (polarCut x r)=polarCut (φ x) r := by
  unfold polarCut
  rw [map_mul,φ.map_cfc (PolarScalar.invCut r) (star x*x)
    (hf:=(PolarScalar.continuous_invCut hr).continuousOn)
    (ha:=(star_mul_self_nonneg x).isSelfAdjoint)
    (hφa:=(map_nonneg φ (star_mul_self_nonneg x)).isSelfAdjoint),map_mul,map_star]

lemma polarCut_left_corner {x q : A} (hqx : q*x=x) (r : ℝ) :
    q*polarCut x r=polarCut x r := by
  unfold polarCut
  rw [← mul_assoc,hqx]

lemma polarCut_right_corner {x p : A} (hp : IsStarProjection p) (hxp : x*p=x) (r : ℝ) :
    polarCut x r*p=polarCut x r := by
  have hpx : p*star x=star x := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hxp
  have hpb : p*(star x*x)=star x*x := by rw [← mul_assoc,hpx]
  have hbp : (star x*x)*p=star x*x := by rw [mul_assoc,hxp]
  have hc : Commute (star x*x) p := hbp.trans hpb.symm
  have hf := hc.cfc_real (PolarScalar.invCut r)
  unfold polarCut
  rw [mul_assoc,hf.eq,← mul_assoc,hxp]


end KaplanskyConsequences.QuasiValue

end

end OAI
