import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.ActualPatchCap
import OAI.Analysis.CoulombIonization.Variational.BoundedDensityPotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma tfPotential_weak_laplacian_ball {ρ : Space → ℝ} (hp : MemLp ρ (5/3))
    {S : ℝ} (hs : Function.support ρ ⊆ ball 0 S)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ ball 0 S) :
    (∫ x, tfPotential ρ x*Δ g x) = -(4*Real.pi)*(∫ x, ρ x*g x) := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density S hp hs
  have hh := tfBallPotential_weak_laplacian S q hg hcg hsg
  simp_rw [hpot] at hh
  have h1 : Function.support (fun x => tfPotential ρ x*Δ g x) ⊆ ball 0 S := by
    intro x hx
    exact hsg (tfLaplacian_support hg (mul_ne_zero_iff.mp hx).2)
  have h2 : Function.support (fun x => ρ x*g x) ⊆ ball 0 S := by
    intro x hx
    exact hsg (subset_tsupport g (mul_ne_zero_iff.mp hx).2)
  rw [ballMeasure_integral_eq_of_support h1] at hh
  have he : (∫ x, q x*g x ∂ballMeasure S) = ∫ x, ρ x*g x ∂ballMeasure S :=
    integral_congr_ae (hq.mono fun x hx => by dsimp only; rw [hx])
  rw [he,ballMeasure_integral_eq_of_support h2] at hh
  exact hh

def nearTFReaction (u : Space → ℝ) (k S : ℝ) : Space → ℝ :=
  (ball 0 S).indicator (fun x => k/(4*Real.pi)*(max (u x) 0)^(3/2:ℝ))

lemma nearTFReaction_measurable {u : Space → ℝ} (hu : Continuous u) (k S : ℝ) :
    Measurable (nearTFReaction u k S) := by
  exact ((measurable_const.mul ((hu.measurable.max measurable_const).pow_const _))).indicator measurableSet_ball

lemma nearTFReaction_nonneg (u : Space → ℝ) {k : ℝ} (hk : 0 ≤ k) (S : ℝ) (x : Space) :
    0 ≤ nearTFReaction u k S x := by
  exact indicator_nonneg (fun _ _ => mul_nonneg (by positivity) (Real.rpow_nonneg (le_max_right _ _) _)) x

lemma nearTFReaction_support (u : Space → ℝ) (k S : ℝ) :
    Function.support (nearTFReaction u k S) ⊆ ball 0 S := support_indicator_subset

lemma nearTFReaction_bound {u : Space → ℝ} {k S B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hu : ∀ x ∈ ball (0 : Space) S, u x ≤ B) (x : Space) :
    nearTFReaction u k S x ≤ k/(4*Real.pi)*B^(3/2:ℝ) := by
  by_cases hx : x ∈ ball (0 : Space) S
  · rw [nearTFReaction,indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_max_right _ _) (max_le (hu x hx) hB) (by norm_num)) (by positivity)
  · rw [nearTFReaction,indicator_of_notMem hx]
    positivity

lemma nearTFReaction_continuous_potential {u : Space → ℝ} (hu : Continuous u)
    {k S B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hb : ∀ x ∈ ball (0 : Space) S, u x ≤ B) :
    Continuous (tfPotential (nearTFReaction u k S)) :=
  tfPotential_continuous
    (bounded_support_integrable (nearTFReaction_measurable hu k S)
      (nearTFReaction_nonneg u hk S) (nearTFReaction_bound hk hB hb) (nearTFReaction_support u k S))
    (bounded_support_memLp (nearTFReaction_measurable hu k S)
      (nearTFReaction_nonneg u hk S) (nearTFReaction_bound hk hB hb) (nearTFReaction_support u k S) (5/3))

theorem nearTFReaction_weak_harmonic {u : Space → ℝ} (hu : Continuous u)
    {k S B T : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hb : ∀ x ∈ ball (0 : Space) S, u x ≤ B) (hST : S ≤ T)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 T → (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ ball 0 S) :
    (∫ x, (u x+tfPotential (nearTFReaction u k S) x)*Δ g x) = 0 := by
  have hcp := nearTFReaction_continuous_potential hu hk hB hb
  have hp := bounded_support_memLp (nearTFReaction_measurable hu k S)
    (nearTFReaction_nonneg u hk S) (nearTFReaction_bound hk hB hb) (nearTFReaction_support u k S) (5/3)
  have he := tfPotential_weak_laplacian_ball hp (nearTFReaction_support u k S) hg hcg hsg
  have h1 : Integrable (fun x => u x*Δ g x) :=
    (hu.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  have h2 : Integrable (fun x => tfPotential (nearTFReaction u k S) x*Δ g x) :=
    (hcp.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  simp_rw [add_mul]
  rw [integral_add h1 h2,he,hw g hg hcg (hsg.trans (ball_subset_ball hST))]
  have hr : (∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) =
      4*Real.pi*(∫ x, nearTFReaction u k S x*g x) := by
    rw [←integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : g x = 0
    · simp only [hx,mul_zero]
    · have hsx := hsg (subset_tsupport g hx)
      rw [nearTFReaction,indicator_of_mem hsx]
      field_simp
  rw [hr]
  ring

end CoulombAnalysis

end

end OAI
