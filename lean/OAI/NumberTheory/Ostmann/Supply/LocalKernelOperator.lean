import OAI.NumberTheory.Ostmann.Supply.KernelMoments
import OAI.NumberTheory.Ostmann.Supply.LocalBlock

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

def localKernelOperator (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) : H →L[ℂ] H :=
  convolutionOperator (fun x => (1+u*(localKernel S t x:ℂ))*(1+v*(localKernel S t x:ℂ)))

def squaredLocalKernelOperator (S : Finset (ZMod p)) (t : ℝ) : H →L[ℂ] H :=
  convolutionOperator (fun x => (localKernel S t x:ℂ)^2)

def localKernelBlock (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) :
    LocalCoordinates Sᶜ →L[ℂ] LocalCoordinates S :=
  localBlock S Sᶜ (localKernelOperator S t u v)

theorem localKernelOperator_decomposition (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) :
    localKernelOperator S t u v = convolutionOperator (fun _ : ZMod p => (1:ℂ)) +
      ((u+v)*(t:ℂ)) • spectralProjection (largeSpectrum S) +
      (u*v) • squaredLocalKernelOperator S t := by
  rw [← convolution_fourierKernel]
  ext f x
  simp only [localKernelOperator,squaredLocalKernelOperator,convolutionOperator_apply,
    add_apply,smul_apply,
    PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,localKernel_cast,
    Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem squaredLocalKernelOperator_norm_le (S : Finset (ZMod p)) (t : ℝ) :
    ‖squaredLocalKernelOperator S t‖ ≤ t^2*((largeSpectrum S).card:ℝ)/p := by
  unfold squaredLocalKernelOperator
  simp only [localKernel_cast]
  simpa only [mul_div_assoc] using squareKernel_norm_le (largeSpectrum S) t

theorem squaredLocalKernelOperator_norm_le_sparse (S : Finset (ZMod p)) (t : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) (hg : gamma S ≤ ε^2)
    (hpos : 0 < density S) (hlt : density S < 1) :
    ‖squaredLocalKernelOperator S t‖ ≤ t^2*ε := by
  have hp : (0:ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hc := (sparse_transform_concentration S hpos hlt hε hε' hg).1
  have hdiv : ((largeSpectrum S).card:ℝ)/p ≤ ε := (div_le_iff₀ hp).mpr hc
  exact (squaredLocalKernelOperator_norm_le S t).trans
    (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiv (sq_nonneg t))

end Ostmann.Supply

end

end OAI
