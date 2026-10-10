import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchTruncationLoss
import OAI.Analysis.CoulombIonization.FieldAnalysis.FineLocalPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfBallPotential_sub_at_zero (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfBallPotential R f 0-tfBallPotential R g 0 =
      ∫ x, (1/‖x‖)*(f-g) x ∂ballMeasure R := by
  rw [tfBallPotential_at_zero,tfBallPotential_at_zero]
  have hf : Integrable (fun x => f x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul (Lp.memLp f) using 1
    funext x
    exact div_eq_inv_mul _ _
  have hg : Integrable (fun x => g x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul (Lp.memLp g) using 1
    funext x
    exact div_eq_inv_mul _ _
  rw [←integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  simp only [hx,Pi.sub_apply]
  ring

lemma tfBallPotential_truncated_triangle {R q : ℝ} (hq : 0 < q) (hqR : q < R)
    (f g : TFLp (ballMeasure R)) {C : ℝ}
    (hg : |tfBallPotential R g 0-(∫ x, (1/max ‖x‖ q)*g x ∂ballMeasure R)| ≤ C) :
    |tfBallPotential R f 0-tfBallPotential R g 0| ≤
      |∫ x, (1/max ‖x‖ q)*(f-g) x ∂ballMeasure R|+
      (∫ x in ball 0 q, ‖f x‖/‖x‖)+C := by
  let A := ∫ x, (1/max ‖x‖ q)*f x ∂ballMeasure R
  let B := ∫ x, (1/max ‖x‖ q)*g x ∂ballMeasure R
  have hp : (∫ x, (1/max ‖x‖ q)*(f-g) x ∂ballMeasure R) = A-B := by
    dsimp only [A,B]
    have hf : Integrable (fun x => (1/max ‖x‖ q)*f x) (ballMeasure R) :=
      (truncated_kernel_memLp R hq).integrable_mul (Lp.memLp f)
    have hg : Integrable (fun x => (1/max ‖x‖ q)*g x) (ballMeasure R) :=
      (truncated_kernel_memLp R hq).integrable_mul (Lp.memLp g)
    rw [←integral_sub hf hg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
  have hf := truncated_potential_remainder hq hqR (Lp.memLp f)
  rw [←tfBallPotential_at_zero] at hf
  rw [hp]
  have he : tfBallPotential R f 0-tfBallPotential R g 0 =
      (A-B)+(tfBallPotential R f 0-A)-(tfBallPotential R g 0-B) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add le_rfl hf) hg))

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

theorem conditionalPatch_full_potential_control {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Finset (Fin M)) (hxy : ∀ i ∈ S, u i ≠ y) (Z lam : ℝ) :
    let Φ := conditionalPatchField ψ t Z lam y R u
    let σ := retainedPatchLp hb S u y R
    let ρ := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    |tfBallPotential R σ 0-tfBallPotential R ρ 0| ≤
      Real.sqrt ((2/q)*tfPatchGap R tfKinetic tfKinetic_pos Φ σ)+
      (∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (u i))+
      2*Real.pi*tfPatchDensityCapConstant*q^2/R^6 := by
  dsimp only
  have hqR' : q < R := by linarith
  have ht := tfBallPotential_truncated_triangle hq hqR' (retainedPatchLp hb S u y R) _
    (conditionalPatchMinimizer_truncation_loss ψ t u hu A hcore y hR hd hr hnuc hsep hq hqR Z lam)
  have hc := Real.abs_le_sqrt (tfPatchGap_truncated_control hq hqR' tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp_nonneg hb S u y R))
  exact ht.trans (add_le_add (add_le_add hc
    (retainedPatchLp_local_potential_le hb hqR'.le S u y hxy)) le_rfl)

end CoulombAtom

end

end OAI
