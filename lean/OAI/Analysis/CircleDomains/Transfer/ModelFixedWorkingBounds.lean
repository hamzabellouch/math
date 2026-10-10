import OAI.Analysis.CircleDomains.Sobolev.ModelUniformJointEnergy

namespace OAI

/-! Common source and image radii for the appending construction.
The estimates are independent of the finite test family. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem exterior_source_mono {G : Set Sphere} {a R : ℝ} (haR : a ≤ R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G) :
    (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G :=
  (compl_subset_compl.mpr (image_mono (ball_subset_ball haR))).trans hsource

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem fixed_working_image_bound (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G)
    {a : ℝ} (ha : 0 < a) (hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G)
    {z : ℂ} (hz : (z : Sphere) ∈ G) (hzn : ‖z‖ ≤ 67*a) : ‖M.function z‖ ≤ 85*a := by
  have hR : 0 < 17*a := by positivity
  have hsource' := exterior_source_mono (show a ≤ 17*a by linarith) hsource
  have hb := (M.uniform_omitted_and_image_bound harea hG hR hsource').2 z hz
    (show ‖z‖ ≤ 4*(17*a) by linarith)
  linarith

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
