import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfReactionCoefficient
import OAI.Analysis.CoulombIonization.ThomasFermi.TFNonradialCap
import OAI.Analysis.CoulombIonization.ThomasFermi.ConditionalPatchPDE
import OAI.Analysis.CoulombIonization.Variational.PatchContinuity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

def tfPatchCapConstant : ℝ := 256*(80/tfReactionCoefficient)^2

lemma tfPatchCapConstant_pos : 0 < tfPatchCapConstant := by
  unfold tfPatchCapConstant
  exact mul_pos (by norm_num) (pow_pos (div_pos (by norm_num) tfReactionCoefficient_pos) _)

lemma tfReactionCoefficient_formula (v : ℝ) :
    4*Real.pi*(max v 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) =
      tfReactionCoefficient*(max v 0)^(3/2:ℝ) := by
  rw [Real.div_rpow (le_max_right _ _) (mul_nonneg (by norm_num) tfKinetic_pos.le)]
  simp only [tfReactionCoefficient,div_eq_mul_inv]
  ring

lemma ballMeasure_integral_eq_of_support {f : Space → ℝ} {R : ℝ}
    (hs : Function.support f ⊆ ball 0 R) : (∫ x, f x ∂ballMeasure R) = ∫ x, f x := by
  rw [ballMeasure,←integral_indicator measurableSet_ball]
  congr 1
  exact indicator_eq_self.2 hs

lemma tf_weak_pde_volume {W : Space → ℝ} {R : ℝ}
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, W x*Δ g x ∂ballMeasure R) = 4*Real.pi*
        (∫ x, (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*g x ∂ballMeasure R))
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball 0 R) :
    (∫ x, W x*Δ g x) = ∫ x, tfReactionCoefficient*(max (W x) 0)^(3/2:ℝ)*g x := by
  have h1 : Function.support (fun x => W x*Δ g x) ⊆ ball (0 : Space) R := by
    intro x hx
    exact hs (tfLaplacian_support hg (mul_ne_zero_iff.mp hx).2)
  have h2 : Function.support (fun x => (max (W x) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*g x)
      ⊆ ball (0 : Space) R := by
    intro x hx
    exact hs (subset_tsupport g (mul_ne_zero_iff.mp hx).2)
  have he := hw g hg hcg hs
  rw [ballMeasure_integral_eq_of_support h1,ballMeasure_integral_eq_of_support h2,←integral_const_mul] at he
  refine he.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
  dsimp only
  rw [←mul_assoc,tfReactionCoefficient_formula]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_nonradial_cap {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) (x : Space) (hx : ‖x‖ ≤ 3*R/4) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    normalizedCoreField Z lam (coreSlice ψ t u) (y+x)-tfBallPotential R f x ≤
      tfPatchCapConstant/R^4 := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  apply weak_tf_nonradial_cap hR tfReactionCoefficient_pos
    (actualPatchField_continuousOn hu A hcore y R hd hr hnuc hsep Z lam f) _ x hx
  intro g hg hcg hs
  apply tf_weak_pde_volume _ hg hcg hs
  intro g hg hcg hs
  exact conditionalPatchMinimizer_weak_pde ψ t u hu A hcore y R hd hr hnuc hsep Z lam hg hcg hs

theorem conditionalPatchMinimizer_density_cap {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    ∀ᵐ x ∂ballMeasure R, ‖x‖ ≤ 3*R/4 →
      f x ≤ (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) := by
  let Φ := conditionalPatchField ψ t Z lam y R u
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
  have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
  have hΦ := conditionalPatchField_ae ψ t Z lam y R u hp
  filter_upwards [tfPatchFunctional_euler R Φ tfKinetic_pos
    (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos Φ)
    (fun g hg => tfPatchMinimizer_min R tfKinetic tfKinetic_pos Φ hg),hΦ] with x he hΦx
  intro hx
  rw [he,hΦx]
  apply Real.rpow_le_rpow (div_nonneg (le_max_right _ _) (mul_nonneg (by norm_num) tfKinetic_pos.le)) _ (by norm_num)
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) tfKinetic_pos.le)
  exact max_le (conditionalPatchMinimizer_nonradial_cap ψ t u hu A hcore y hR hd hr hnuc hsep Z lam x hx)
    (div_nonneg tfPatchCapConstant_pos.le (pow_nonneg hR.le _))

end CoulombAtom

end

end OAI
