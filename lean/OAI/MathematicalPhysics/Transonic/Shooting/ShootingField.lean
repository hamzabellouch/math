import OAI.MathematicalPhysics.Transonic.Shooting.ShootingBounds
import OAI.MathematicalPhysics.Transonic.Shooting.AxisBarriersCore
import OAI.MathematicalPhysics.Transonic.Exterior.Parameters

namespace OAI

section
noncomputable section

namespace SepticProfile.ShootingParameters
open Set
lemma sigma_contDiffOn : ContDiffOn ℝ 1 sigma (Icc leftEnd rightEnd) := by
  apply ContDiffOn.div
  · unfold d; fun_prop
  · unfold e; fun_prop
  · intro t ht
    have he := e_pos ht
    positivity
lemma kappa_contDiffOn : ContDiffOn ℝ 1 kappa (Icc leftEnd rightEnd) := by
  apply ContDiffOn.div
  · fun_prop
  · unfold e; fun_prop
  · intro t ht
    exact ne_of_gt (mul_pos (by norm_num) (e_pos ht))
end SepticProfile.ShootingParameters

namespace SepticProfile.ShootingField
open Set AxisBarriers ShootingParameters

lemma D_positive {s z u cap : ℝ} (hs0 : 0 ≤ s) (hs : s<1)
    (hz : z ∈ Ioc (0:ℝ) 1) (hcap : cap<1) (hu : u ∈ Icc 0 cap) : 0<D s z u := by
  have hz2 : z^2≤1 := by nlinarith [mul_nonneg (by linarith [hz.2] : 0≤1-z) (by linarith [hz.1] : 0≤1+z)]
  have hu2 : u^2<1 := by nlinarith [mul_pos (by linarith [hu.2] : 0<1-u) (by linarith [hu.1] : 0<1+u)]
  have hm : s*z^2 ≤ s := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hz2)]
  exact mul_pos (mul_pos hz.1 (by linarith)) (by linarith)

def field (p : ℝ × (ℝ×ℝ)) : ℝ := N (kappa p.2.1) p.1 p.2.2/D (sigma p.2.1) p.1 p.2.2

lemma field_contDiffOn {a b cap : ℝ} (ha : 0<a) (hb : b≤1) (hcap : cap<1) :
    ContDiffOn ℝ 1 field (Icc a b ×ˢ (Icc leftEnd rightEnd ×ˢ Icc 0 cap)) := by
  let S := Icc a b ×ˢ (Icc leftEnd rightEnd ×ˢ Icc 0 cap)
  have hpar : MapsTo (fun p : ℝ×(ℝ×ℝ) => p.2.1) S (Icc leftEnd rightEnd) := fun p hp => hp.2.1
  have hs := sigma_contDiffOn.comp (contDiffOn_snd.fst) hpar
  have hk := kappa_contDiffOn.comp (contDiffOn_snd.fst) hpar
  have hN : ContDiffOn ℝ 1 (fun p : ℝ×(ℝ×ℝ) => N (kappa p.2.1) p.1 p.2.2) S := by
    unfold N
    fun_prop
  have hD : ContDiffOn ℝ 1 (fun p : ℝ×(ℝ×ℝ) => D (sigma p.2.1) p.1 p.2.2) S := by
    unfold D
    fun_prop
  exact hN.div hD (fun p hp => ne_of_gt (D_positive
    (by linarith [(sigma_shooting_bounds hp.2.1).1])
    (by linarith [(sigma_shooting_bounds hp.2.1).2])
    ⟨ha.trans_le hp.1.1,hp.1.2.trans hb⟩ hcap hp.2.2))

end SepticProfile.ShootingField

end
end

end OAI
