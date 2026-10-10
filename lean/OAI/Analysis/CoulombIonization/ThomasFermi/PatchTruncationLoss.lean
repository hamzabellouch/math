import Mathlib
import OAI.Analysis.CoulombIonization.Variational.PotentialRecovery
import OAI.Analysis.CoulombIonization.ThomasFermi.TFNonradialOscillation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

def tfPatchDensityCapConstant : ℝ :=
  (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)

lemma tfPatchDensityCapConstant_pos : 0 < tfPatchDensityCapConstant := by
  exact Real.rpow_pos_of_pos (div_pos tfPatchCapConstant_pos (mul_pos (by norm_num) tfKinetic_pos)) _

lemma tfPatchDensityCap_scale {R : ℝ} (hR : 0 < R) :
    (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) = tfPatchDensityCapConstant/R^6 := by
  have he : tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic) =
      (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))/R^4 := by ring
  rw [he,cap_reaction_scale (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) hR]
  rfl

lemma local_coulomb_le_of_density_cap {f : TFSpace → ℝ} {q C : ℝ}
    (hq : 0 < q) (hf : MemLp f (5/3) (ballMeasure q))
    (hcap : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ C) :
    (∫ x in ball 0 q, ‖f x‖/‖x‖) ≤ 2*Real.pi*C*q^2 := by
  have hi : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure q) := by
    convert! (nuclear_memLp q).integrable_mul hf.norm using 1
    funext x
    exact div_eq_inv_mul _ _
  have hk : Integrable (fun x : TFSpace => ‖x‖⁻¹) (ballMeasure q) := by
    simpa only [one_div] using (nuclear_memLp q).integrable (Fact.out : (1 : ENNReal) ≤ 5/2)
  have hh : (∫ x, ‖f x‖/‖x‖ ∂ballMeasure q) ≤ ∫ x, C*‖x‖⁻¹ ∂ballMeasure q := by
    apply integral_mono_ae hi (hk.const_mul C)
    filter_upwards [hcap] with x hx
    exact (div_le_div_of_nonneg_right hx (norm_nonneg x)).trans_eq (by ring)
  apply hh.trans_eq
  rw [integral_const_mul]
  change C*(∫ x : TFSpace in ball 0 q, ‖x‖⁻¹) = _
  rw [integral_coulomb_ball hq]
  ring

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_truncation_loss {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r q : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (Z lam : ℝ) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    |tfBallPotential R f 0-(∫ x, (1/max ‖x‖ q)*f x ∂ballMeasure R)| ≤
      2*Real.pi*tfPatchDensityCapConstant*q^2/R^6 := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  have hqR' : q < R := by linarith
  have hmeasure : ballMeasure q ≤ ballMeasure R :=
    Measure.restrict_mono (ball_subset_ball hqR'.le) le_rfl
  have hcap := conditionalPatchMinimizer_density_cap ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
  have hn := tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  have hn' := ae_mono hmeasure hn
  have hc' := ae_mono hmeasure hcap
  have hb : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ tfPatchDensityCapConstant/R^6 := by
    filter_upwards [hn',hc',ae_restrict_mem measurableSet_ball] with x hx hxcap hxb
    rw [Real.norm_of_nonneg hx]
    have hnorm : ‖x‖ ≤ 3*R/4 := (mem_ball_zero_iff.mp hxb).le.trans hqR
    simpa only [tfPatchDensityCap_scale hR] using hxcap hnorm
  have he := truncated_potential_remainder hq hqR' (Lp.memLp f)
  rw [←tfBallPotential_at_zero] at he
  apply he.trans
  have hh := local_coulomb_le_of_density_cap hq ((Lp.memLp f).mono_measure hmeasure) hb
  exact hh.trans_eq (by ring)

end CoulombAtom

end

end OAI
