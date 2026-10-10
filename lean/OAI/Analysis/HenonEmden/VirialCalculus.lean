import OAI.Analysis.HenonEmden.Gradients

namespace OAI

section VirialCalculus

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open WeakPDE RadialCalculus

lemma regular_energyDensity {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x) (q B : ℝ) :
    ContDiffOn ℝ 2 (energyDensity u q B) ({0}ᶜ : Set (Space n)) := by
  exact ((contDiffOn_id.norm ℝ (fun x hx => by simpa using hx)).rpow_const_of_ne
    (fun x hx => norm_ne_zero_iff.mpr (by simpa using hx))).mul
      (hu.rpow_const_of_ne (fun x _ => ne_of_gt (hup x)))

lemma dir_energyDensity {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (q B : ℝ) {x : Space n} (hx : x ≠ 0) (e : Space n) :
    dir (energyDensity u q B) e x =
      B*inner ℝ x e/‖x‖^2*energyDensity u q B x+(q+1)*source u q B x*dir u e x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have huD := (hu.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).differentiableAt (by norm_num)
  have hrD := hasFDerivAt_profile_norm hx (Real.hasDerivAt_rpow_const (p := B) (Or.inl hr.ne'))
  have hpD := huD.hasFDerivAt.rpow_const (p := q+1) (Or.inl (hup x).ne')
  have hD := hrD.mul hpD
  change HasFDerivAt (energyDensity u q B) _ x at hD
  rw [dir,hD.fderiv]
  simp only [add_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  rw [show q+1-1=q by ring,source_off_zero _ _ _ hx]
  unfold energyDensity dir
  rw [Real.rpow_sub hr,Real.rpow_one]
  field_simp
  ring

lemma weighted_virial_scalar_test {n : ℕ} {u φ : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u ({0}ᶜ : Set (Space n))) (hup : ∀ x, 0 < u x)
    (q B : ℝ) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφ0 : 0 ∉ tsupport φ) (e : Space n) :
    (∫ x, energyDensity u q B x*dir φ e x) =
      -(∫ x, (B*inner ℝ x e/‖x‖^2*energyDensity u q B x+
        (q+1)*source u q B x*dir u e x)*φ x) := by
  have hF := regular_energyDensity hu hup q B
  have hs : tsupport φ ⊆ ({0}ᶜ : Set (Space n)) := by
    intro x hx; simp only [mem_compl_iff,mem_singleton_iff]; intro hx0; subst x; exact hφ0 hx
  have hφD : ContDiff ℝ 0 (dir φ e) := contDiffOn_univ.mp (contDiffOn_dir hφ.contDiffOn isOpen_univ e)
  have hFc : ContinuousOn (dir (energyDensity u q B) e) ({0}ᶜ : Set (Space n)) :=
    (contDiffOn_dir (k := 1) hF isOpen_compl_singleton e).continuousOn
  have hi1 : Integrable (fun x => dir (energyDensity u q B) e x*φ x) :=
    integrable_mul_compact hφc (hFc.mono hs) hφ.continuous.continuousOn
  have hi2 : Integrable (fun x => energyDensity u q B x*dir φ e x) :=
    integrable_mul_compact (compactSupport_dir hφc e)
      (hF.continuousOn.mono ((tsupport_dir_subset φ e).trans hs)) hφD.continuous.continuousOn
  have hi3 : Integrable (fun x => energyDensity u q B x*φ x) :=
    integrable_mul_compact hφc (hF.continuousOn.mono hs) hφ.continuous.continuousOn
  have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := energyDensity u q B) (g := φ) (v := e) hi1 hi2 hi3
    (fun x hx => (hF.contDiffAt (isOpen_compl_singleton.mem_nhds (hs hx))).differentiableAt (by norm_num))
    (fun x _ => hφ.differentiable (by norm_num) x)
  change (∫ x, energyDensity u q B x*dir φ e x) = -(∫ x, dir (energyDensity u q B) e x*φ x) at hI
  rw [hI]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport φ
  · rw [dir_energyDensity hu hup q B (hs hx) e]
  · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,mul_zero]

end HenonLaneEmden
end
end VirialCalculus

end OAI
