import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.NearTFReaction
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierNuclearBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma bounded_density_weak_poisson {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  obtain ⟨S,_,hS⟩ := hc.isCompact.isBounded.exists_pos_norm_lt
  apply tfPotential_weak_laplacian_ball (bounded_support_memLp hm hn hb hs (5/3))
    (S := max R S)
  · exact hs.trans (ball_subset_ball (le_max_left _ _))
  · exact hφ
  · exact hc
  · intro x hx
    exact mem_ball_zero_iff.mpr ((hS x hx).trans_le (le_max_right _ _))

def initialOffset (Z r a : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  -tfPotential ρ x-(7/10)*Z/r+a*‖x‖^2

def initialBranch (Z r a : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  nuclearField Z x+initialOffset Z r a ρ x

lemma initialOffset_continuous {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ) :
    Continuous (initialOffset Z r a ρ) := by
  exact ((tfPotential_continuous (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3))).neg.sub continuous_const).add
      (continuous_const.mul (continuous_norm.pow 2))

lemma initial_polynomial_laplacian (Z r a : ℝ) (x : TFSpace) :
    Δ (fun y : TFSpace => (-(7/10)*Z/r+a*‖y‖^2 : ℝ)) x = 6*a := by
  have hd := (contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun y : TFSpace => ‖y‖^2))
  have ha := ContDiffAt.laplacian_add (x := x)
    (contDiffAt_const (c := (-(7/10)*Z/r : ℝ)))
    ((contDiffAt_const (c := a)).mul hd.contDiffAt)
  change Δ ((fun _ : TFSpace => (-(7/10)*Z/r : ℝ)) + (fun y : TFSpace => a*‖y‖^2)) x = 6*a
  rw [ha,laplacian_const,Pi.zero_apply,zero_add]
  have he := laplacian_smul (x := x) a hd.contDiffAt
  simp only [smul_eq_mul] at he
  change Δ (a • (fun y : TFSpace => ‖y‖^2)) x = 6*a
  rw [he, CoulombPDE.laplacian_norm_sq]
  norm_num [TFSpace,finrank_euclideanSpace_fin]
  ring

lemma initialOffset_weak_poisson {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, initialOffset Z r a ρ x*Δ φ x) = ∫ x, (4*Real.pi*ρ x+6*a)*φ x := by
  have hp := tfPotential_continuous (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3))
  let q : TFSpace → ℝ := fun y => -(7/10)*Z/r+a*‖y‖^2
  have hq : ContDiff ℝ 2 q := contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))
  have he : initialOffset Z r a ρ = fun x => -tfPotential ρ x+q x := by funext x; dsimp [initialOffset,q]; ring
  have hρ : LocallyIntegrable ρ := (bounded_support_integrable hm hn hb hs).locallyIntegrable
  rw [he]
  simp_rw [add_mul,neg_mul]
  rw [integral_add (f := fun x => -(tfPotential ρ x * Δ φ x)) (g := fun x => q x * Δ φ x) (locallyIntegrable_mul_test hp.locallyIntegrable (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)).neg
    (locallyIntegrable_mul_test hq.continuous.locallyIntegrable (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
    integral_neg,bounded_density_weak_poisson hm hn hb hs hφ hc,neg_mul,neg_neg,
    compact_laplacian_green hq hφ hc]
  have hl : Δ q = fun _ => 6*a := funext (initial_polynomial_laplacian Z r a)
  rw [hl]
  have hi : Integrable (fun x => 4*Real.pi*ρ x*φ x) := by
    simpa only [mul_assoc] using (locallyIntegrable_mul_test hρ hφ.continuous hc).const_mul (4*Real.pi)
  rw [integral_add hi ((hφ.continuous.integrable_of_hasCompactSupport hc).const_mul (6*a))]
  congr 1
  calc
    _ = ∫ x, (4*Real.pi)*(ρ x*φ x) := (integral_const_mul (4*Real.pi) _).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by dsimp only; ring)

theorem initialBranch_weak_nuclear {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M R : ℝ} (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hs : Function.support ρ ⊆ ball 0 R) (Z r a : ℝ) :
    WeakNuclearLowerOn univ Z (initialBranch Z r a ρ) (fun x => 4*Real.pi*ρ x+6*a) := by
  apply (weakNuclearLower_add_iff Z (initialOffset_continuous hm hn hb hs Z r a).locallyIntegrable).mpr
  intro φ hφ hc _ _
  exact (initialOffset_weak_poisson hm hn hb hs Z r a hφ hc).ge

end CoulombBarrier

end

end OAI
