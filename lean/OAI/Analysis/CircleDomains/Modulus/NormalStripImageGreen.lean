import OAI.Analysis.CircleDomains.Modulus.NormalStripRectangleGreen

namespace OAI

/-! Green's identity on the physical image of a normal-coordinate half
rectangle, with its actual Euclidean area measure. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma integral_normal_strip_image_rectangle {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (a b c d : ℝ)
    (hi : InjOn (curveNormalStrip γ) (Icc (a,c) (b,d)))
    (hj : ∀ p ∈ Icc (a,c) (b,d),
      0 ≤ planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p)) (q : ℂ → ℝ) :
    (∫ z in (curveNormalStrip γ) '' (Ioo a b ×ˢ Ioo c d), q z) =
      ∫ p in Icc (a,c) (b,d),
        planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) * q (curveNormalStrip γ p) := by
  have hsub : Ioo a b ×ˢ Ioo c d ⊆ Icc (a,c) (b,d) := by
    rintro p ⟨hp,hq⟩
    exact ⟨⟨hp.1.le,hq.1.le⟩,⟨hp.2.le,hq.2.le⟩⟩
  rw [integral_image_planarMap (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun p _ => ((curveNormalStrip_contDiff hγ).differentiable (by simp) p).hasFDerivAt)
    (hi.mono hsub)]
  calc
    _ = ∫ p in Ioo a b ×ˢ Ioo c d,
        planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) * q (curveNormalStrip γ p) := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [abs_of_nonneg (hj p (hsub hp))]
    _ = _ := by
      rw [← Icc_prod_Icc,Measure.volume_eq_prod]
      exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

end CircleDomainRigidity

end

end OAI
