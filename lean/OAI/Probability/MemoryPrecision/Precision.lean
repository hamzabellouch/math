import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelAdmissibility
import OAI.Probability.MemoryPrecision.KernelStream
import OAI.Probability.MemoryPrecision.Reflection

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open MemoryPrecision NoiselessRegression

lemma precision_from_exact_bound {d M T : ℕ} {ε C A : ℝ}
    (hd : 32 ≤ d) (hT : d ≤ 4*T) (hC : 0 < C) (hA : 0 < A)
    (hM : (M:ℝ) ≤ A*(d:ℝ)^2) (hε : 0 < ε)
    (hb : (2/3:ℝ) ≤
      (2*ε*Real.exp (C*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2)) :
    (1/(8+20*C*(1+A)))*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdp : (d:ℝ) ≤ 4*T := by exact_mod_cast hT
  let q := (d-1)/8
  let b := BlockCount T q
  let a := ((d:ℝ)-1)/2
  let X := C*(1+(M:ℝ)/(d:ℝ)^2)*(b:ℝ)
  have hq : 0 < q := by dsimp [q]; omega
  have hdq : (d:ℝ) ≤ 16*(q:ℝ) := by
    exact_mod_cast (show d ≤ 16*q by dsimp [q]; omega)
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hbd : (b:ℝ)*(d:ℝ) ≤ 20*T := by
    have hceil : (b:ℝ) ≤ (T:ℝ)/q+1 :=
      (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ (T:ℝ)/q)).le
    calc
      _ ≤ ((T:ℝ)/q+1)*d := mul_le_mul_of_nonneg_right hceil hd0.le
      _ = ((T:ℝ)/q)*d+d := by ring
      _ ≤ ((T:ℝ)/q)*(16*q)+d := by gcongr
      _ = 16*T+d := by field_simp
      _ ≤ _ := by linarith
  have ha : 1 ≤ a := by
    dsimp [a]
    have : (32:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have ha0 : 0 < a := by linarith
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2/3) hb
  change Real.log (2/3:ℝ) ≤ Real.log ((2*ε*Real.exp X)^a) at hlog
  rw [Real.log_rpow (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_mul (by norm_num) hε.ne'] at hlog
  have hl2 : Real.log 2 ≤ (1:ℝ) := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2) using 1
    norm_num
  have hl23 : -(1:ℝ) ≤ Real.log (2/3:ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2/3)
    norm_num at h
    linarith
  have hle : Real.log (1/ε) ≤ 2+X := by
    have hmul := mul_le_mul_of_nonneg_left hl2 ha0.le
    have he : Real.log (1/ε) = -Real.log ε := by simp
    rw [he]
    nlinarith
  have hmem : (M:ℝ)/(d:ℝ)^2 ≤ A := (div_le_iff₀ (sq_pos_of_pos hd0)).2 hM
  have hX : X*(d:ℝ) ≤ 20*C*(1+A)*T := by
    calc
      _ = C*(1+(M:ℝ)/(d:ℝ)^2)*((b:ℝ)*d) := by dsimp [X]; ring
      _ ≤ C*(1+A)*((b:ℝ)*d) := by gcongr
      _ ≤ C*(1+A)*(20*T) := mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = _ := by ring
  have hfinal : (d:ℝ)*Real.log (1/ε) ≤ (8+20*C*(1+A))*T := by
    have hh := mul_le_mul_of_nonneg_left hle hd0.le
    nlinarith
  have hp : 0 < 8+20*C*(1+A) := by positivity
  calc
    _ = ((d:ℝ)*Real.log (1/ε))/(8+20*C*(1+A)) := by ring
    _ ≤ _ := (div_le_iff₀ hp).2 (by nlinarith)

namespace Policy
lemma source_uniform_of_pointwise {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hL : Admissible L ρ (UniformSphere d)) (ε : ℝ)
    (hs : ∀ s, (2/3:ℝ≥0∞) ≤ FixedSuccess L ρ ε s) :
    (2/3:ℝ≥0∞) ≤ Success L ρ (UniformSphere d) ε := by
  let : NeZero d := ⟨hd.ne'⟩
  have hm := hL.experiment (angleTest ε) (measurable_angleTest ε) (angleTest_le_one ε)
  unfold Success
  rw [lintegral_prod _ hm]
  calc
    _ = ∫⁻ _s : MemoryPrecision.Kernel.Sphere d, (2/3:ℝ≥0∞) ∂UniformSphere d := by simp
    _ ≤ _ := lintegral_mono hs

lemma source_precision {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 32 ≤ d) (hL : Admissible L ρ (UniformSphere d)) {ε A : ℝ}
    (hA : 0 < A) (hM : (M:ℝ) ≤ A*(d:ℝ)^2) (hε : 0 < ε) (hε1 : ε ≤ 1/10)
    (hs : (2/3:ℝ≥0∞) ≤ Success L ρ (UniformSphere d) ε) :
    (1/(8+20*StreamConstant*(1+A)))*(d:ℝ)*Real.log (1/ε) ≤ (T:ℝ) := by
  have hT : d ≤ 4*T := by
    by_contra hn
    have hb := hs.trans (source_linear_success_bound L ρ (by omega) (by omega) hε1 hL)
    have hb' : ENNReal.ofReal (2/3:ℝ) ≤ ENNReal.ofReal (21/32:ℝ) := by
      simpa [ENNReal.ofReal_div_of_pos] using hb
    have hh := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 21/32)).mp hb'
    norm_num at hh
  have hb := hs.trans (source_stream_explicit d M T hd ε hε hε1 Ω ρ inferInstance L hL)
  have hb' : (2/3:ℝ) ≤
      (2*ε*Real.exp (StreamConstant*(1+(M:ℝ)/(d:ℝ)^2)*(BlockCount T ((d-1)/8):ℝ)))^(((d:ℝ)-1)/2) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa [ENNReal.ofReal_div_of_pos] using hb.trans (min_le_right _ _)
  exact precision_from_exact_bound hd hT streamConstant_pos hA hM hε hb'
end Policy
end MemoryPrecision.Kernel


end

end OAI
