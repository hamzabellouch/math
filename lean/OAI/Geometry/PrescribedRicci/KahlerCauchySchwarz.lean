import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference
import OAI.Geometry.PrescribedRicci.KahlerEnergyChain
import OAI.Geometry.PrescribedRicci.KahlerGreenIdentity
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy

namespace OAI

/-! Kahler Cauchy Schwarz. -/

section

 

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma energy_realSMul_left (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A)
    (a : ℝ) (x : X) : (g.energy (ψ.realSMul a) φ).value x = a * (g.energy ψ φ).value x := by
  change (g.energy (ψ.compose (fun t => a * t) (contDiff_const.mul contDiff_id)) φ).value x = _
  have hd : deriv (fun t => a * t) (ψ.value x) = a := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id (ψ.value x)).const_mul a).deriv
  rw [g.energy_comp_left, hd]

lemma energy_constant_left (g : KaehlerMetric A) (φ : SmoothRealFunction A) (a : ℝ) (x : X) :
    (g.energy (SmoothRealFunction.constant a) φ).value x = 0 := by
  change (g.energy ((SmoothRealFunction.constant (A := A) 0).compose (fun _ => a) contDiff_const) φ).value x = _
  rw [g.energy_comp_left, deriv_const, zero_mul]

variable [T2Space X] [CompactSpace X]

lemma integral_laplacian (g : KaehlerMetric A) (φ : SmoothRealFunction A) :
    g.integral (g.laplacian φ).value = 0 := by
  have h := g.green_identity (SmoothRealFunction.constant 1) φ
  have he : (g.energy (SmoothRealFunction.constant 1) φ).value = fun _ => 0 :=
    funext (g.energy_constant_left φ 1)
  rw [he, g.integral_zero, neg_zero] at h
  simpa only [SmoothRealFunction.constant, one_mul] using h

lemma integral_cauchySchwarz (g : KaehlerMetric A) {f h : X → ℝ}
    (hf : Continuous f) (hh : Continuous h) :
    (g.integral (fun x => f x * h x)) ^ 2 ≤
      g.integral (fun x => f x ^ 2) * g.integral (fun x => h x ^ 2) := by
  have hq (t : ℝ) : 0 ≤ g.integral (fun x => f x ^ 2) * (t*t) +
      (2 * g.integral (fun x => f x * h x)) * t + g.integral (fun x => h x ^ 2) := by
    calc
      0 ≤ g.integral (fun x => (t * f x + h x) ^ 2) := g.integral_nonneg (fun _ => sq_nonneg _)
      _ = _ := by
        have he : (fun x => (t*f x+h x)^2) =
            fun x => (t*t) * (f x)^2 + (2*t) * (f x*h x) + (h x)^2 := by funext x; ring
        rw [he, g.integral_add
          (f := fun x => (t*t) * f x ^ 2 + (2*t) * (f x*h x))
          (h := fun x => h x ^ 2)
          ((continuous_const.fun_mul (hf.pow 2)).fun_add (continuous_const.fun_mul (hf.fun_mul hh)))
          (hh.pow 2), g.integral_add
          (f := fun x => (t*t) * f x ^ 2) (h := fun x => (2*t) * (f x*h x))
          (continuous_const.fun_mul (hf.pow 2)) (continuous_const.fun_mul (hf.fun_mul hh)),
          g.integral_const_mul, g.integral_const_mul]
        ring
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

omit [T2Space X] [CompactSpace X] in
lemma energy_add_right (g : KaehlerMetric A) (φ ψ χ : SmoothRealFunction A) :
    (g.energy φ (ψ.addFunction χ)).value =
      fun x => (g.energy φ ψ).value x + (g.energy φ χ).value x := by
  rw [g.energy_symm, g.energy_add_left, g.energy_symm ψ φ, g.energy_symm χ φ]

omit [T2Space X] [CompactSpace X] in
lemma energy_realSMul_right (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A)
    (a : ℝ) (x : X) : (g.energy ψ (φ.realSMul a)).value x = a * (g.energy ψ φ).value x := by
  rw [g.energy_symm, g.energy_realSMul_left, g.energy_symm φ ψ]

lemma energy_cauchySchwarz (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A) :
    (g.integral (g.energy φ ψ).value) ^ 2 ≤
      g.integral (g.energy φ φ).value * g.integral (g.energy ψ ψ).value := by
  have he (t : ℝ) (x : X) :
      (g.energy ((φ.realSMul t).addFunction ψ) ((φ.realSMul t).addFunction ψ)).value x =
        (t*t) * (g.energy φ φ).value x + (2*t) * (g.energy φ ψ).value x + (g.energy ψ ψ).value x := by
    simp only [g.energy_add_left, g.energy_add_right, g.energy_realSMul_left,
      g.energy_realSMul_right, g.energy_symm ψ φ]
    ring
  have hq (t : ℝ) : 0 ≤ g.integral (g.energy φ φ).value * (t*t) +
      (2 * g.integral (g.energy φ ψ).value) * t + g.integral (g.energy ψ ψ).value := by
    calc
      0 ≤ g.integral (g.energy ((φ.realSMul t).addFunction ψ) ((φ.realSMul t).addFunction ψ)).value :=
        g.integral_nonneg (g.energy_nonneg _)
      _ = _ := by
        rw [show (g.energy ((φ.realSMul t).addFunction ψ) ((φ.realSMul t).addFunction ψ)).value =
          (fun x => (t*t) * (g.energy φ φ).value x + (2*t) * (g.energy φ ψ).value x +
            (g.energy ψ ψ).value x) from funext (he t)]
        rw [g.integral_add ((continuous_const.fun_mul (g.energy φ φ).continuous).fun_add
          (continuous_const.fun_mul (g.energy φ ψ).continuous)) (g.energy ψ ψ).continuous,
          g.integral_add (continuous_const.fun_mul (g.energy φ φ).continuous)
          (continuous_const.fun_mul (g.energy φ ψ).continuous), g.integral_const_mul, g.integral_const_mul]
        ring
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
