import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothMultiplier

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace L2Multiplier
open MeasureTheory
open scoped ComplexConjugate ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
lemma inner_clm_real_right (f : α → ℂ) (hf : MemLp f ∞ μ)
    (hreal : ∀ x, conj (f x) = f x) (u v : Lp ℂ 2 μ) :
    inner ℂ u (clm f hf v) = inner ℂ (clm f hf u) v := by
  simpa only [show (fun x ↦ conj (f x)) = f from funext hreal] using
    inner_clm_right f hf u v

lemma clm_comm (f g : α → ℂ) (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ)
    (u : Lp ℂ 2 μ) : clm f hf (clm g hg u) = clm g hg (clm f hf u) := by
  rw [← clm_mul, ← clm_mul]
  congr 2
  exact mul_comm f g

end L2Multiplier
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate ENNReal
lemma SmoothMultiplier.partial_real {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) (p : Direction N) (X : Configuration N L) :
    conj (coordDerivative N L f.toFun p X) = coordDerivative N L f.toFun p X := by
  have he : (fun X ↦ conj (f.toFun X)) = f.toFun := funext hf
  rw [← congrFun (coordDerivative_conj (f.smooth.differentiable (by simp)) p) X, he]

def SmoothMultiplier.derivativeScalar {N : ℕ} {L : Length} (f : SmoothMultiplier N L)
    (p : Direction N) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  L2Multiplier.clm _ (f.partial_memLp_top p)

@[simp] lemma SmoothMultiplier.onJet_fst {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (u : Jet N L) : (f.onJet u).1 = f.onScalar u.1 := rfl

@[simp] lemma SmoothMultiplier.onJet_snd {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (u : Jet N L) (p : Direction N) :
    (f.onJet u).2 p = f.onScalar (u.2 p) + f.derivativeScalar p u.1 := rfl

lemma SmoothMultiplier.inner_onScalar_right {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (hf : ∀ X, conj (f.toFun X) = f.toFun X)
    (u v : ScalarL2 N L) : inner ℂ u (f.onScalar v) = inner ℂ (f.onScalar u) v :=
  L2Multiplier.inner_clm_real_right _ _ hf u v

lemma SmoothMultiplier.inner_derivativeScalar_right {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (hf : ∀ X, conj (f.toFun X) = f.toFun X)
    (p : Direction N) (u v : ScalarL2 N L) :
    inner ℂ u (f.derivativeScalar p v) = inner ℂ (f.derivativeScalar p u) v :=
  L2Multiplier.inner_clm_real_right _ _ (f.partial_real hf p) u v

lemma SmoothMultiplier.onScalar_derivativeScalar_comm {N : ℕ} {L : Length}
    (f : SmoothMultiplier N L) (p : Direction N) (u : ScalarL2 N L) :
    f.onScalar (f.derivativeScalar p u) = f.derivativeScalar p (f.onScalar u) :=
  L2Multiplier.clm_comm _ _ _ _ u

theorem IsGroundVector.smooth_multiplier_identity {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) (f : SmoothMultiplier N L)
    (hf : ∀ X, conj (f.toFun X) = f.toFun X) :
    energy (f.onJet u) - energy u * ‖f.onScalar u.1‖ ^ 2 =
      ∑ p : Direction N, ‖f.derivativeScalar p u.1‖ ^ 2 := by
  have hv := f.onJet_mem_domain (f.onJet_mem_domain hu.1)
  have he := hu.full_first_variation (f.onJet (f.onJet u)) hv
  have hnorm (x : ScalarL2 N L) : (inner ℂ x x).re = ‖x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  have hpair (p : Direction N) :
      (inner ℂ (u.2 p) ((f.onJet (f.onJet u)).2 p)).re =
        ‖f.onScalar (u.2 p)‖ ^ 2 +
          2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re := by
    rw [f.onJet_snd, f.onJet_snd, f.onJet_fst, map_add,
      inner_add_right, inner_add_right, ← f.onScalar_derivativeScalar_comm,
      f.inner_onScalar_right hf (u.2 p) (f.onScalar (u.2 p)),
      f.inner_onScalar_right hf (u.2 p) (f.derivativeScalar p u.1)]
    simp only [Complex.add_re, hnorm]
    ring
  have hs : (inner ℂ u.1 (f.onJet (f.onJet u)).1).re = ‖f.onScalar u.1‖ ^ 2 := by
    rw [f.onJet_fst, f.onJet_fst, f.inner_onScalar_right hf, hnorm]
  have her := congrArg Complex.re he
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hs, hpair] at her
  change (∑ p, ‖(f.onJet u).2 p‖ ^ 2) - energy u * ‖f.onScalar u.1‖ ^ 2 = _
  simp only [f.onJet_snd, norm_add_sq (𝕜 := ℂ)]
  rw [← her]
  change (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re +
      ‖f.derivativeScalar p u.1‖ ^ 2)) -
    (∑ p, (‖f.onScalar (u.2 p)‖ ^ 2 +
      2 * (inner ℂ (f.onScalar (u.2 p)) (f.derivativeScalar p u.1)).re)) = _
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end HardSphere

end

end OAI
