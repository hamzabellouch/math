import OAI.Analysis.CircleDomains.Topology.CompactPlanarCurl

namespace OAI

/-! A form supported strictly inside the Jordan domain has zero boundary
integral and zero total curl integral. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma interior_local_green {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) (ε : ℝ)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q)
    (hPs : tsupport P ⊆ jordanInterior H) (hQs : tsupport Q ⊆ jordanInterior H) :
    ε * planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hb : planarFormIntegral P Q γ = 0 := by
    unfold planarFormIntegral
    calc
      _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _
        have hn : γ t ∉ jordanInterior H := by
          intro ht
          exact (hγ.mem_frontier t).2 ((jordanInterior_isOpen H).interior_eq.symm ▸ ht)
        have hp := image_eq_zero_of_notMem_tsupport (f := P) (fun h => hn (hPs h))
        have hq := image_eq_zero_of_notMem_tsupport (f := Q) (fun h => hn (hQs h))
        dsimp only
        rw [hp,hq,zero_mul,zero_mul,zero_add]
      _ = 0 := by simp
  have hi : (∫ z in jordanInterior H,
      (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) =
      ∫ z, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with z hz
    exact planar_curl_zero_off_support hPs hQs hz
  rw [hb,mul_zero,hi,integral_compact_planar_curl hP hQ hcP hcQ]

end CircleDomainRigidity

end

end OAI
