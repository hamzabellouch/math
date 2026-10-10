import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiValue
import OAI.Analysis.Kaplansky.Ultrapower.PolarScalar

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
open PolarScalar
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def polarCut (x : A) (r : ℝ) : A := x * cfc (invCut r) (star x*x)
def spectralCut (x : A) (r : ℝ) : A := cfc (cut r) (star x*x)

lemma polarCut_square (x : A) {r : ℝ} (hr : 0 < r) :
    star (polarCut x r)*polarCut x r=spectralCut x r := by
  have hf := (continuous_invCut hr).continuousOn (s:=spectrum ℝ (star x*x))
  have hb : IsSelfAdjoint (star x*x) := (star_mul_self_nonneg x).isSelfAdjoint
  have hsa : IsSelfAdjoint (cfc (invCut r) (star x*x)) := IsSelfAdjoint.cfc
  unfold polarCut spectralCut
  rw [star_mul,hsa.star_eq]
  calc
    cfc (invCut r) (star x*x)*star x*(x*cfc (invCut r) (star x*x)) =
      cfc (invCut r) (star x*x)*(star x*x)*cfc (invCut r) (star x*x) := by noncomm_ring
    _ = cfc (fun t => invCut r t*t*invCut r t) (star x*x) := by
      rw [cfc_mul (fun t => invCut r t*t) (invCut r) _ (hf.mul continuousOn_id) hf,
        cfc_mul (invCut r) (fun t => t) _ hf continuousOn_id,cfc_id' ℝ (star x*x) hb]
    _ = cfc (cut r) (star x*x) := by congr 1; funext t; exact cut_eq hr t

lemma spectralCut_nonneg (x : A) {r : ℝ} (hr : 0 < r) : 0 ≤ spectralCut x r := by
  rw [← polarCut_square x hr]
  exact star_mul_self_nonneg _

lemma spectralCut_norm (x : A) {r : ℝ} (hr : 0 < r) : ‖spectralCut x r‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (cut_nonneg hr (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht))]
  exact cut_le_one hr

lemma polarCut_norm (x : A) {r : ℝ} (hr : 0 < r) : ‖polarCut x r‖ ≤ 1 := by
  have h := spectralCut_norm x hr
  rw [← polarCut_square x hr,CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (polarCut x r)]

lemma cfc_sqrt_real (a : A) (ha : 0 ≤ a) : cfc Real.sqrt a=CFC.sqrt a := by
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact (cfcₙ_eq_cfc (f:=Real.sqrt) (a:=a)).symm

lemma polarCut_error_square (x : A) {r : ℝ} (hr : 0 < r) :
    star (polarCut x r*CFC.sqrt (star x*x)-x)*(polarCut x r*CFC.sqrt (star x*x)-x) =
      cfc (fun t => t*(invCut r t*Real.sqrt t-1)^2) (star x*x) := by
  let b := star x*x
  have hb : IsSelfAdjoint b := (star_mul_self_nonneg x).isSelfAdjoint
  have hf := (continuous_invCut hr).continuousOn (s:=spectrum ℝ b)
  have hg : ContinuousOn (fun t => invCut r t*Real.sqrt t-1) (spectrum ℝ b) :=
    (hf.mul Real.continuous_sqrt.continuousOn).sub continuousOn_const
  have he : polarCut x r*CFC.sqrt b-x = x*cfc (fun t => invCut r t*Real.sqrt t-1) b := by
    rw [cfc_sub (fun t => invCut r t*Real.sqrt t) (fun _ => 1) b (hf.mul Real.continuous_sqrt.continuousOn) continuousOn_const,
      cfc_mul (invCut r) Real.sqrt _ hf Real.continuous_sqrt.continuousOn,cfc_const_one ℝ b,
      cfc_sqrt_real b (star_mul_self_nonneg x)]
    unfold polarCut
    noncomm_ring
  change star (polarCut x r*CFC.sqrt b-x)*(polarCut x r*CFC.sqrt b-x)=_
  rw [he,star_mul,(IsSelfAdjoint.cfc (f:=fun t => invCut r t*Real.sqrt t-1) (a:=b)).star_eq]
  calc
    cfc (fun t => invCut r t*Real.sqrt t-1) b*star x*(x*cfc (fun t => invCut r t*Real.sqrt t-1) b) =
      cfc (fun t => invCut r t*Real.sqrt t-1) b*b*cfc (fun t => invCut r t*Real.sqrt t-1) b := by dsimp [b]; noncomm_ring
    _ = cfc (fun t => (invCut r t*Real.sqrt t-1)*t*(invCut r t*Real.sqrt t-1)) b := by
      rw [cfc_mul (fun t => (invCut r t*Real.sqrt t-1)*t) (fun t => invCut r t*Real.sqrt t-1) _ (hg.mul continuousOn_id) hg,cfc_mul (fun t => invCut r t*Real.sqrt t-1) (fun t => t) _ hg continuousOn_id,cfc_id' ℝ b hb]
    _ = _ := by congr 1; funext t; ring

lemma polarCut_error_norm (x : A) {r : ℝ} (hr : 0 < r) :
    ‖polarCut x r*CFC.sqrt (star x*x)-x‖^2 ≤ r := by
  rw [pow_two,← CStarRing.norm_star_mul_self,polarCut_error_square x hr]
  apply norm_cfc_le hr.le
  intro t ht
  have h := cut_error hr (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht)
  simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2


end KaplanskyConsequences.QuasiValue

end

end OAI
