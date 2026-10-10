import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

namespace OAI

/-! # The quantitative entropy deficit of a separated branch

This is the scalar rearrangement in the branching argument of Rajala--Sturm,
arXiv:1207.6754, proof of Theorem 1.1, pp. 10--11. The three chord inequalities
retain the curvature error and the separation entropy explicitly.
-/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem branch_entropy_deficit {t ε A M E U D H L : ℝ}
    (ht0 : 0≤t) (ht1 : t≤1)
    (hmean : H=(U+D)/2-L)
    (hfirst : (t+ε)*E≤ε*M+t*H+A*t*ε*(t+ε))
    (hup : (1-t)*U≤(1-t-ε)*E+ε*M+A*ε*(1-t-ε)*(1-t))
    (hdown : (1-t)*D≤(1-t-ε)*E+ε*M+A*ε*(1-t-ε)*(1-t)) :
    t*(1-t)*L≤ε*(M-E+A*t*(1-t)) := by
  have hm : (1-t)*((U+D)/2)≤(1-t-ε)*E+ε*M+A*ε*(1-t-ε)*(1-t) := by
    linarith only [hup,hdown]
  have h₀ := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr ht1)
  have h₁ := mul_le_mul_of_nonneg_left hm ht0
  rw [hmean] at h₀
  nlinarith only [h₀,h₁]

theorem branch_entropy_deficit_of_lower_bound {t ε A M E U D H L B : ℝ}
    (ht0 : 0≤t) (ht1 : t≤1) (hε : 0≤ε) (hB : B≤E)
    (hmean : H=(U+D)/2-L)
    (hfirst : (t+ε)*E≤ε*M+t*H+A*t*ε*(t+ε))
    (hup : (1-t)*U≤(1-t-ε)*E+ε*M+A*ε*(1-t-ε)*(1-t))
    (hdown : (1-t)*D≤(1-t-ε)*E+ε*M+A*ε*(1-t-ε)*(1-t)) :
    t*(1-t)*L≤ε*(M-B+A*t*(1-t)) := by
  exact (branch_entropy_deficit ht0 ht1 hmean hfirst hup hdown).trans
    (mul_le_mul_of_nonneg_left (by linarith) hε)

theorem tendsto_branch_entropy_budget (C B A : ℝ) :
    Tendsto (fun ε : ℝ => ε*(C-Real.log ε-B+A)) (𝓝[>] 0) (𝓝 0) := by
  have hlin : Tendsto (fun ε : ℝ => ε*(C-B+A)) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    simpa using hid.mul_const (C-B+A)
  have hlog : Tendsto (fun ε : ℝ => ε*Real.log ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_mul_log.continuousAt (x:=0)).tendsto.mono_left
      (nhdsWithin_le_nhds (s:=Ioi 0))
  have h := hlin.sub hlog
  simp only [sub_zero] at h
  convert h using 1
  funext ε
  ring

theorem exists_small_branch_budget {c : ℝ} (hc : 0<c) (C B A : ℝ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ε*(C-Real.log ε-B+A)<c :=
  (tendsto_branch_entropy_budget C B A).eventually (Iio_mem_nhds hc)

end RegularPointCoordinates

end OAI
