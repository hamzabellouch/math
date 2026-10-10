import OAI.Analysis.LipschitzHilbert.Fourier.FiniteTimeKernelMoment

namespace OAI

/-! The exact telescoping identity behind the finite Hilbert time-kernel
decomposition. The cutoff profile will be constructed independently. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finiteTimeKernel_telescope (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) :
    (t : ℂ)*finiteTimeKernel k N topLength t=
      a ((2:ℝ)^N*t/(2*topLength))-a (t/(2*topLength)) := by
  have hterm (j : Fin N) : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
      a ((2:ℝ)^(j.val+1)*t/(2*topLength))-a ((2:ℝ)^j.val*t/(2*topLength)) := by
    have hl : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
    have heq : (t : ℂ)*scaledTimeKernel k (topLength/(2:ℝ)^j.val) t=
        ((t/(topLength/(2:ℝ)^j.val) : ℝ) : ℂ)*k (t/(topLength/(2:ℝ)^j.val)) := by
      unfold scaledTimeKernel
      push_cast
      ring
    rw [heq,hprofile]
    have harg : t/(topLength/(2:ℝ)^j.val)=(2:ℝ)^(j.val+1)*t/(2*topLength) := by
      rw [pow_succ]
      field_simp
    have hhalf : (t/(topLength/(2:ℝ)^j.val))/2=(2:ℝ)^j.val*t/(2*topLength) := by
      field_simp
    rw [harg]
    congr 1
    rw [←harg,hhalf]
  unfold finiteTimeKernel
  rw [Finset.mul_sum]
  simp_rw [hterm]
  change (∑ j : Fin N, (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) j.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    a ((2:ℝ)^(n+1)*t/(2*topLength))-a ((2:ℝ)^n*t/(2*topLength))) N]
  simpa only [pow_zero,one_mul] using
    Finset.sum_range_sub (fun n : ℕ => a ((2:ℝ)^n*t/(2*topLength))) N

def profileKernelDifference (a : ℝ → ℂ) (r R t : ℝ) : ℂ :=
  (a (t/r)-a (t/R))/(t : ℂ)

theorem finiteTimeKernel_eq_profileDifference (k : SchwartzMap ℝ ℂ) (a : ℝ → ℂ)
    (hprofile : ∀ s : ℝ, (s : ℂ)*k s=a s-a (s/2))
    (N : ℕ) (topLength : ℝ) (htop : 0<topLength) (t : ℝ) (ht : t≠0) :
    finiteTimeKernel k N topLength t=
      profileKernelDifference a (2*topLength/(2:ℝ)^N) (2*topLength) t := by
  have h := finiteTimeKernel_telescope k a hprofile N topLength htop t
  have harg : t/(2*topLength/(2:ℝ)^N)=(2:ℝ)^N*t/(2*topLength) := by field_simp
  unfold profileKernelDifference
  rw [harg]
  apply (eq_div_iff (by exact_mod_cast ht : (t:ℂ)≠0)).2
  simpa only [mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
