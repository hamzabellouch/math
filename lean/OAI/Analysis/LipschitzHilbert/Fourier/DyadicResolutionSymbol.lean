import OAI.Analysis.LipschitzHilbert.Fourier.DyadicSmoothCutoff
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Exact telescoping and strong pointwise resolution for the binary
low-pass differences used in the commutator decomposition. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def dyadicResolutionScale (N n : ℕ) : ℝ := (1/2:ℝ)^N*(2:ℝ)^n

theorem dyadicResolutionScale_pos (N n : ℕ) : 0<dyadicResolutionScale N n := by
  unfold dyadicResolutionScale
  positivity

def dyadicResolutionSymbol (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n∈Finset.range (2*N+1), dyadicDifference (dyadicResolutionScale N n*x)

theorem dyadicDifference_telescope (M : ℕ) (x : ℝ) :
    (∑ n∈Finset.range M, dyadicDifference ((2:ℝ)^n*x))=
      reassemblyLow (x/2)-reassemblyLow (((2:ℝ)^M*x)/2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,dyadicDifference_apply,pow_succ]
    have he : (2^M*2*x)/2=(2:ℝ)^M*x := by ring
    rw [he]
    ring

theorem dyadicResolutionSymbol_eq (N : ℕ) (x : ℝ) :
    dyadicResolutionSymbol N x=
      reassemblyLow ((1/2:ℝ)^(N+1)*x)-reassemblyLow ((2:ℝ)^N*x) := by
  unfold dyadicResolutionSymbol
  have he (n : ℕ) : dyadicResolutionScale N n*x=(2:ℝ)^n*((1/2:ℝ)^N*x) := by
    unfold dyadicResolutionScale
    ring
  simp_rw [he]
  rw [dyadicDifference_telescope]
  have hfirst : ((1/2:ℝ)^N*x)/2=(1/2:ℝ)^(N+1)*x := by rw [pow_succ]; ring
  have hcancel : (2:ℝ)^N*(1/2:ℝ)^N=1 := by rw [←mul_pow]; norm_num
  have hlast : ((2:ℝ)^(2*N+1)*((1/2:ℝ)^N*x))/2=(2:ℝ)^N*x := by
    rw [show 2*N+1=N+N+1 by omega,pow_succ,pow_add]
    calc
      _ = ((2:ℝ)^N*(1/2:ℝ)^N)*(2:ℝ)^N*x := by ring
      _ = _ := by rw [hcancel,one_mul]
  rw [hfirst,hlast]

theorem dyadicResolutionSymbol_norm (N : ℕ) (x : ℝ) :
    ‖dyadicResolutionSymbol N x‖≤2 := by
  rw [dyadicResolutionSymbol_eq]
  have h1 := reassemblyLow_norm ((1/2:ℝ)^(N+1)*x)
  have h2 := reassemblyLow_norm ((2:ℝ)^N*x)
  exact (norm_sub_le _ _).trans (by linarith only [h1,h2])

theorem dyadicResolutionSymbol_tendsto (x : ℝ) (hx : x≠0) :
    Tendsto (fun N : ℕ => dyadicResolutionSymbol N x) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun N : ℕ => reassemblyLow ((1/2:ℝ)^(N+1)*x)) atTop (𝓝 1) := by
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const ((1/2:ℝ)*x)
    have hh := reassemblyLow.continuous.continuousAt.tendsto.comp hp
    simpa only [Function.comp_def,zero_mul,pow_succ,mul_assoc,reassemblyLow_one 0 (by norm_num)] using hh
  have hlarge : ∀ᶠ N : ℕ in atTop, reassemblyLow ((2:ℝ)^N*x)=0 := by
    have hp := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const
      (show 0 < |x| from abs_pos.mpr hx)
    filter_upwards [hp.eventually (eventually_ge_atTop (13/12:ℝ))] with N hN
    apply reassemblyLow_zero
    simpa only [abs_mul,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) N)] using hN
  have hz : Tendsto (fun N : ℕ => reassemblyLow ((2:ℝ)^N*x)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hlarge.mono fun _ h => h.symm)
  simpa only [dyadicResolutionSymbol_eq,sub_zero] using hsmall.sub hz

end LipschitzHilbert.PacketRepresentation

end

end OAI
