import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.BinKernel
import OAI.MeasureTheory.Falconer.Fourier.DistanceBandKernelBound
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Estimates.MinimalMaskNestedSupport

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal
variable {d n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState d)

lemma width_kernel (z : ℝ × ℝ) :
    1/(1+|z.1-z.2|/e.width)^2=1/(1+(2:ℝ)^e.t*|z.1-z.2|)^2 := by
  simp only [width,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,
    div_eq_mul_inv,inv_inv,mul_comm]

lemma distance_self_kernel [IsFiniteMeasure e.ρ] :
    e.normalization*(∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+(2:ℝ)^e.t*|z.1-z.2|)^2)
      ∂e.distance.prod e.distance)≤binKernelConstant*e.coincidence := by
  have hw : 0<e.width := by unfold width; positivity
  have h := real_bin_decaying_self_kernel_bound e.distance hw
  simp_rw [e.width_kernel] at h
  have hc : (e.distance.prod e.distance) {z : ℝ × ℝ | |z.1-z.2|≤e.width}≤
      (e.distance.prod e.distance) {z : ℝ × ℝ | |z.1-z.2|≤100*(d+1)*e.width} := by
    apply measure_mono
    intro z hz
    change |z.1-z.2|≤100*(d+1)*e.width
    change |z.1-z.2|≤e.width at hz
    apply hz.trans
    have hd : (0:ℝ)≤d := Nat.cast_nonneg d
    nlinarith
  have hh := mul_le_mul_right (h.trans (mul_le_mul_right hc binKernelConstant)) e.normalization
  rw [e.distance_collision] at hh
  simpa only [coincidence,mul_left_comm] using hh

lemma normalized_weight_factor :
    ENNReal.ofReal ((2:ℝ)^((e.t:ℝ)-e.a))*ENNReal.ofReal (e.levelMass^(-2:ℤ))*
      ENNReal.ofReal (e.levelMass^(-2:ℤ))=e.normalization := by
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
  ring

lemma normalized_dominated_distance_kernel [IsFiniteMeasure e.ρ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) • e.distance) :
    ENNReal.ofReal ((2:ℝ)^((e.t:ℝ)-e.a)) *
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+(2:ℝ)^e.t*|z.1-z.2|)^2) ∂μ.prod μ)≤
        binKernelConstant*e.coincidence := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+(2:ℝ)^e.t*|z.1-z.2|)^2)
  have hp := Measure.prod_mono hμ hμ
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul] at hp
  have h := lintegral_mono' hp (fun z => le_refl (F z))
  rw [lintegral_smul_measure,smul_eq_mul] at h
  have hh := mul_le_mul_right h (ENNReal.ofReal ((2:ℝ)^((e.t:ℝ)-e.a)))
  rw [← mul_assoc,← mul_assoc,e.normalized_weight_factor] at hh
  exact hh.trans e.distance_self_kernel

lemma dominated_distance_band [IsFiniteMeasure e.ρ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ≤ENNReal.ofReal (e.levelMass^(-2:ℤ)) • e.distance) :
    (2:ℝ)^(-(e.a:ℝ))*(∫ r in Icc (-((2:ℝ)^e.t)) ((2:ℝ)^e.t), ‖charFun μ r‖^2)≤
      (32*binKernelConstant.toReal)*e.coincidence.toReal := by
  have h := mul_le_mul_right (distance_band_kernel_bound_ennreal μ
    (by positivity : 0<(2:ℝ)^e.t)) (ENNReal.ofReal ((2:ℝ)^(-(e.a:ℝ))))
  have hkernel := mul_le_mul_right (e.normalized_dominated_distance_kernel μ hμ) (32:ℝ≥0∞)
  have he : (2:ℝ)^(-(e.a:ℝ))*(32*(2:ℝ)^e.t)=32*(2:ℝ)^((e.t:ℝ)-e.a) := by
    rw [mul_left_comm,← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 2
    ring
  have hc : ENNReal.ofReal ((2:ℝ)^(-(e.a:ℝ)))*ENNReal.ofReal (32*(2:ℝ)^e.t)=
      32*ENNReal.ofReal ((2:ℝ)^((e.t:ℝ)-e.a)) := by
    rw [← ENNReal.ofReal_mul (by positivity),he,ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [← mul_assoc,hc,mul_assoc] at h
  have hh := h.trans hkernel
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top binKernelConstant_ne_top e.coincidence_ne_top)) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg ‖charFun μ r‖)),
    ENNReal.toReal_mul,ENNReal.toReal_mul] at hr
  norm_num only [ENNReal.toReal_ofNat] at hr
  simpa only [mul_assoc] using hr

end PositiveDistanceState

theorem uniform_actual_prefix_low_band {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)) [IsFiniteMeasure e.ρ],
      N₀≤e.N → e.sig=sig → e.J=J → 0<e.q → e.t≤e.N →
      ∀ K : ℝ, 32*(n+2:ℝ)≤K → e.X.length=e.a → e.Y.length=e.a →
      farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
      ∀ v≤e.t, (2:ℝ)^(-(e.a:ℝ)) *
        (∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun e.weightedDistance r‖^2)≤
        (32*binKernelConstant.toReal)*
          ({e with t:=v,i:=e.i+1} : PositiveDistanceState (n+1)).coincidence.toReal := by
  obtain ⟨N₀,h₀⟩ := PositiveDistanceState.uniform_weightedDistance_nested_domination (n:=n) hsig hJ
  refine ⟨N₀,?_⟩
  intro e he hN hsig' hJ' hq ht K hK hX hY hs v hv
  let := e.weightedDistance_isFinite hK hX hY hs
  exact ({e with t:=v,i:=e.i+1} : PositiveDistanceState (n+1)).dominated_distance_band
    e.weightedDistance (h₀ e hN hsig' hJ' hq ht K hK hX hY hs v hv)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
