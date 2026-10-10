import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyJets
import OAI.MathematicalPhysics.Transonic.Shooting.ClampedFamily
import OAI.MathematicalPhysics.Transonic.Shooting.ShootingField
import OAI.MathematicalPhysics.Transonic.Shooting.RegularGlobalControl

namespace OAI

section
noncomputable section

namespace SepticProfile.RegularFamily
open Set SourceFamily RegularContinuation ShootingParameters

def field (p : ℝ×(ℝ×ℝ)) : ℝ := -ShootingField.field (99/100-p.1,p.2)

lemma field_contDiffOn : ContDiffOn ℝ 1 field
    (Icc (0:ℝ) (9/100) ×ˢ (Icc leftEnd rightEnd ×ˢ Icc 0 (999/1000))) := by
  have hf := ShootingField.field_contDiffOn (a:=9/10) (b:=99/100) (cap:=999/1000)
    (by norm_num) (by norm_num) (by norm_num)
  have hc : ContDiffOn ℝ 1 (fun p:ℝ×(ℝ×ℝ) => (99/100-p.1,p.2))
      (Icc (0:ℝ) (9/100) ×ˢ (Icc leftEnd rightEnd ×ˢ Icc 0 (999/1000))) := by fun_prop
  exact (hf.comp hc (fun p hp => ⟨⟨by linarith [hp.1.2],by linarith [hp.1.1]⟩,hp.2⟩)).neg

lemma field_eq (t x u : ℝ) : field (x,t,u)=
    -IntegerPolynomial.numer (kappa t) (99/100-x) u/IntegerPolynomial.denom (sigma t) (99/100-x) u := by
  unfold field ShootingField.field AxisBarriers.N AxisBarriers.D IntegerPolynomial.numer IntegerPolynomial.denom
  ring

theorem exists_family (seed : Parameter → ℝ) (hseed : Continuous seed) :
    ∃ u : Parameter → ℝ → ℝ,
      Continuous (fun p : Parameter × ↥(Icc (0:ℝ) (9/100)) => u p.1 p.2) ∧
      (∀ t, u t 0=seed t) ∧
      ∀ t x, x ∈ Icc (0:ℝ) (9/100) → HasDerivWithinAt (u t)
        (IntegerPolynomial.globalField (sig t) (kap t) x (u t x)) (Icc 0 (9/100)) x := by
  obtain ⟨u,huc,hu0,hud⟩ := exists_continuous_clamped_family (by norm_num : (0:ℝ)≤9/100)
    (by norm_num [leftEnd,rightEnd]) (by norm_num : (0:ℝ)≤999/1000)
    field_contDiffOn (fun a:Parameter => a.val) seed continuous_subtype_val hseed (fun a => a.property)
  refine ⟨u,huc,hu0,?_⟩
  intro t x hx
  convert hud t x hx using 1
  exact (field_eq t x (clamp 0 (999/1000) (u t x))).symm

end SepticProfile.RegularFamily

end
end

end OAI
