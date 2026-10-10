import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.MatrixH1Smooth
import OAI.Geometry.TamingCompatibility.DifferentialForms.QuantitativeInterior

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap LineDeriv Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma small_principal_local_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ‖perturbation (F := F) n a‖ ≤ 1/2)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (χ η : 𝓢(E,ℂ)) (hη : ∀ x ∈ tsupport χ, η =ᶠ[nhds x] fun _ => 1)
    (u : 𝓢'(E,F)) (f : H E F n) (v : H E F ((n:ℝ)+2)) (w : H E F ((n:ℝ)+1))
    (hv : toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ u)
    (hw : toDistribution E F ((n:ℝ)+1) w = smulLeftCLM F η u)
    (heq : smulLeftCLM F χ (perturbedHelmholtz a u + matrixLowerOrder b L d c K u) =
      smulLeftCLM F χ (toDistribution E F n f)) :
    ‖v‖ ≤ 2 * (‖product (F := F) n χ‖ * ‖f‖ +
      (‖product (F := F) n χ‖ * ‖matrixLowerH n b L d c K‖ +
        ‖localizationErrorH (F := F) n a χ‖) * ‖w‖) := by
  have hlocal : smulLeftCLM F χ
      (perturbedHelmholtz a (toDistribution E F ((n:ℝ)+1) w) +
       matrixLowerOrder b L d c K (toDistribution E F ((n:ℝ)+1) w)) =
      smulLeftCLM F χ (toDistribution E F n f) := by
    rw [hw,map_add,perturbedHelmholtz_locality a χ η hη,
      matrixLowerOrder_locality b L d c K χ η hη,← map_add]
    exact heq
  rw [map_add] at hlocal
  let y := product n χ f - product n χ (matrixLowerH n b L d c K w) + localizationErrorH n a χ w
  have hy : perturbedHelmholtz a (toDistribution E F ((n:ℝ)+2) v) =
      toDistribution E F n y := by
    rw [hv,← cutoff_mul_cutoff χ η hη u,← hw,perturbedHelmholtz_cutoff]
    rw [eq_sub_of_add_eq hlocal]
    simp only [y,map_add,map_sub,toDistribution_product,matrixLowerH_spec,localizationErrorH_spec]
  have hb := perturbedHelmholtz_half_bound n a ha v y hy
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have h₁ := (product (F := F) n χ).le_opNorm f
  have h₂ := (product (F := F) n χ).le_opNorm (matrixLowerH n b L d c K w)
  have h₃ := (matrixLowerH n b L d c K).le_opNorm w
  have h₄ := (localizationErrorH (F := F) n a χ).le_opNorm w
  have h₂' := mul_le_mul_of_nonneg_left h₃ (norm_nonneg (product (F := F) n χ))
  have hn := norm_add_le (product n χ f - product n χ (matrixLowerH n b L d c K w))
    (localizationErrorH n a χ w)
  have hs := norm_sub_le (product n χ f) (product n χ (matrixLowerH n b L d c K w))
  change ‖product n χ f - product n χ (matrixLowerH n b L d c K w) +
    localizationErrorH n a χ w‖ ≤ _
  nlinarith
end TamingCompatibility.HilbertSobolev

end

end OAI
