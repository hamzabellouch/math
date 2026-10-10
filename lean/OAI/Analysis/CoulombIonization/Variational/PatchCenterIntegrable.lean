import Mathlib
import OAI.Analysis.CoulombIonization.Localization.PatchCenterObservable
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchTruncationLoss

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchMinimizer_potential_zero_le {R T F : ℝ} (hR : 0 < R)
    (hT : 0 < T) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    tfBallPotential R (tfPatchMinimizer R T hT Φ) 0 ≤
      2*Real.pi*((max F 0/((5/3:ℝ)*T))^(3/2:ℝ))*R^2 := by
  have hn := tfPatchMinimizer_nonneg R T hT Φ
  have hb := tfPatchMinimizer_ae_bound hT Φ hΦ
  have he := local_coulomb_le_of_density_cap hR (Lp.memLp (tfPatchMinimizer R T hT Φ))
    (hb.and hn |>.mono fun x hx => by simpa only [Real.norm_of_nonneg hx.2] using hx.1)
  apply le_trans _ he
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [zero_sub,norm_neg,Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

def weightedPatchCenter {N M : ℕ} (ψ : FormVector (N+M)) (t : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) (u : Configuration M) : ℝ :=
  formMass (coreSlice ψ t u)*conditionalPatchCenter ψ t Z lam y R u

lemma conditionalPatchCenter_abs_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    ∀ᵐ u, |conditionalPatchCenter ψ t Z lam y R u| ≤
      finiteCorePatchBound N Z lam b +
        2*Real.pi*((finiteCorePatchBound N Z lam b/((5/3:ℝ)*tfKinetic))^(3/2:ℝ))*R^2 := by
  have hy : y ∈ closedBall y R := mem_closedBall_self hR.le
  filter_upwards [hψ.ae_coreSlice t,
    conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hsep] with u hu hf
  have h1 := normalizedCoreField_abs_le hu A (hcore u) hb y
    (fun a ha => hsep a ha y hy) hb (hnuc y hy) Z lam
  have h2 := tfPatchMinimizer_potential_zero_le hR tfKinetic_pos _ hf
  rw [max_eq_left (finiteCorePatchBound_nonneg N Z lam hb)] at h2
  have hn := tfBallPotential_nonneg (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u)) 0
  exact (abs_sub _ _).trans (add_le_add h1 (by simpa only [abs_of_nonneg hn] using h2))

lemma weightedPatchCenter_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    Integrable (weightedPatchCenter ψ t Z lam y R) := by
  have hbnd := conditionalPatchCenter_abs_le hψ t y hR Z lam hb A hcore hnuc hsep
  have hm := (conditionalPatchCenter_aemeasurable hψ t Z lam y R).aestronglyMeasurable
  exact ((hψ.coreSlice_mass_integrable t).bdd_mul hm
    (hbnd.mono fun u hu => by simpa only [Real.norm_eq_abs] using hu)).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
