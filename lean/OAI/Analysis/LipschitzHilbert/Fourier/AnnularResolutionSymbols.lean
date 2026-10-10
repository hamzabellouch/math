import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSquareBound
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The concrete symmetric finite annular partition converges to one away
from the zero vertical frequency. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

def reassemblyScale (N n : ℕ) : ℝ := (2/3:ℝ)^N*(3/2:ℝ)^n

theorem reassemblyScale_pos (N n : ℕ) : 0<reassemblyScale N n := by
  unfold reassemblyScale
  positivity

def reassemblySymbol (N : ℕ) (s : ℝ) : ℂ :=
  ∑ n∈Finset.range (2*N+1), reassemblyDifference (reassemblyScale N n*s)

theorem reassemblyScale_last (N : ℕ) :
    (3/2:ℝ)^(2*N+1)*(2/3:ℝ)^N=(3/2:ℝ)^(N+1) := by
  have hcancel : (3/2:ℝ)^N*(2/3:ℝ)^N=1 := by
    rw [←mul_pow]
    norm_num
  rw [show 2*N+1=N+(N+1) by omega,pow_add]
  calc
    _ = ((3/2:ℝ)^N*(2/3:ℝ)^N)*(3/2:ℝ)^(N+1) := by ring
    _ = _ := by rw [hcancel,one_mul]

theorem reassemblySymbol_eq (N : ℕ) (s : ℝ) :
    reassemblySymbol N s=
      reassemblyLow ((16/27)*(2/3:ℝ)^N*s)-
        reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)*s) := by
  unfold reassemblySymbol
  have he (n : ℕ) : reassemblyScale N n*s=(3/2:ℝ)^n*((2/3:ℝ)^N*s) := by
    unfold reassemblyScale
    ring
  simp_rw [he]
  rw [reassemblyDifference_telescope]
  congr 1
  · congr 1
    ring
  · congr 1
    calc
      _ = (16/27)*((3/2:ℝ)^(2*N+1)*(2/3:ℝ)^N)*s := by ring
      _ = _ := by rw [reassemblyScale_last]

theorem reassemblySymbol_norm (N : ℕ) (s : ℝ) : ‖reassemblySymbol N s‖≤2 := by
  rw [reassemblySymbol_eq]
  exact (norm_sub_le _ _).trans (by linarith only [reassemblyLow_norm ((16/27)*(2/3:ℝ)^N*s), reassemblyLow_norm ((16/27)*(3/2:ℝ)^(N+1)*s)])

theorem reassemblyLow_small_tendsto (s : ℝ) :
    Tendsto (fun N : ℕ => reassemblyLow ((16/27)*(2/3:ℝ)^N*s)) atTop (𝓝 1) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2/3)
    (by norm_num : (2/3:ℝ)<1)
  have hs := ((tendsto_const_nhds (x:=(16/27:ℝ))).mul hp).mul_const s
  have h := reassemblyLow.continuous.continuousAt.tendsto.comp hs
  simpa only [mul_zero,zero_mul,reassemblyLow_one 0 (by norm_num),Function.comp_def] using h

theorem reassemblyLow_large_eventually (s : ℝ) (hs : s≠0) :
    ∀ᶠ N : ℕ in atTop, reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)*s)=0 := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3/2)
  have hscale : Tendsto (fun N : ℕ => ((16/27)*(3/2)*|s|)*(3/2:ℝ)^N) atTop atTop :=
    hp.const_mul_atTop (by positivity)
  filter_upwards [hscale.eventually (eventually_ge_atTop (13/12:ℝ))] with N hN
  apply reassemblyLow_zero
  convert hN using 1
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16/27),
    abs_of_pos (by positivity : (0:ℝ)<(3/2:ℝ)^(N+1)),pow_succ]
  ring

theorem reassemblySymbol_tendsto (s : ℝ) (hs : s≠0) :
    Tendsto (fun N : ℕ => reassemblySymbol N s) atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => reassemblyLow ((16/27)*(3/2:ℝ)^(N+1)*s)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((reassemblyLow_large_eventually s hs).mono (fun _ h => h.symm))
  simpa only [reassemblySymbol_eq,sub_zero] using (reassemblyLow_small_tendsto s).sub hz

end LipschitzHilbert.PacketRepresentation

end

end OAI
