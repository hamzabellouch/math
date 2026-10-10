import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridDifferentiation
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Twice continuous coordinate differentiability of the literal
Eisenstein sum, from the existing local summable derivative bounds. -/
noncomputable section
open Set
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicTheta_twice_contDiffAt_tsum {ι : Type*} {f : ι → ℝ → ℂ}
    {u₁ u₂ : ι → ℝ} (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    {a b x : ℝ} (hx : x∈Ioo a b)
    (hf : ∀ i t, t∈Ioo a b → AnalyticAt ℝ (f i) t)
    (h₁ : ∀ i t, t∈Ioo a b → ‖deriv (f i) t‖≤u₁ i)
    (h₂ : ∀ i t, t∈Ioo a b → ‖deriv (deriv (f i)) t‖≤u₂ i)
    (h₀ : ∀ t∈Ioo a b, Summable (fun i => f i t)) :
    ContDiffAt ℝ 2 (fun t => ∑' i, f i t) x := by
  have hd t (ht : t∈Ioo a b) := cubicTheta_twice_hasDerivAt_tsum hu₁ hu₂ ht hf h₁ h₂ (h₀ t ht)
  have hc₂ : ContinuousOn (fun t => ∑' i, deriv (deriv (f i)) t) (Ioo a b) :=
    continuousOn_tsum (fun i t ht => (hf i t ht).deriv.deriv.continuousAt.continuousWithinAt) hu₂ h₂
  have hc : ContinuousOn (deriv (deriv (fun t => ∑' i, f i t))) (Ioo a b) :=
    hc₂.congr (fun t ht => (hd t ht).2.1.deriv)
  have hcd₁ : ContDiffOn ℝ 1 (deriv (fun t => ∑' i, f i t)) (Ioo a b) := by
    rw [show (1 : ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    exact ⟨fun t ht => (hd t ht).2.1.differentiableAt.differentiableWithinAt,
      by norm_num,contDiffOn_zero.mpr hc⟩
  have hcd₂ : ContDiffOn ℝ 2 (fun t => ∑' i, f i t) (Ioo a b) := by
    rw [show (2 : ℕ∞ω)=1+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    exact ⟨fun t ht => (hd t ht).1.differentiableAt.differentiableWithinAt,by norm_num,hcd₁⟩
  exact hcd₂.contDiffAt (isOpen_Ioo.mem_nhds hx)

theorem cubicThetaEisenstein_coordinate_contDiffAt
    (k : CubicThetaAxis) (s : ℂ) (hs : 2<s.re) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s)
      (cubicThetaCoordinateCenter k x y v) := by
  obtain ⟨r,hr,u₁,u₂,hu₁,hu₂,hbound⟩ := cubicThetaCoordinate_local_jets k s hs x y hv
  have he : (fun t => cubicThetaEisenstein (cubicThetaCoordinateLine k x y v t) s)=
      (fun t => ∑' cd, cubicThetaEisensteinGridTerm cd (cubicThetaCoordinateLine k x y v t) s) :=
    funext (fun t => cubicThetaEisenstein_eq_grid _ _)
  rw [he]
  exact cubicTheta_twice_contDiffAt_tsum hu₁ hu₂ ⟨by linarith,by linarith⟩
    (fun cd t ht => cubicThetaCoordinateLine_analytic k cd s x y v t (hbound cd t ht).1)
    (fun cd t ht => (hbound cd t ht).2.1)
    (fun cd t ht => (hbound cd t ht).2.2)
    (fun t ht => cubicThetaEisensteinGrid_summable (hbound (0,0) t ht).1 hs)

end CubicFirstMoment

end

end OAI
