import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.KahlerIntegration
import OAI.Geometry.PrescribedPotential.GlobalOperator
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference

namespace OAI

/-! Global Kahler Energy. -/

section

 

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

 
def energy (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A) : SmoothRealFunction A where
  value x := ((g.laplacian (ψ.product φ)).value x -
    ψ.value x * (g.laplacian φ).value x - φ.value x * (g.laplacian ψ).value x) / 2
  smooth i := (((g.laplacian (ψ.product φ)).smooth i).sub
    ((ψ.smooth i).mul ((g.laplacian φ).smooth i))).sub
      ((φ.smooth i).mul ((g.laplacian ψ).smooth i)) |>.div_const 2

lemma energy_local (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A)
    (i : Fin A.count) {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (g.energy ψ φ).localExpression i z =
      (gradientPair (g.matrix i z) (holRealDeriv (ψ.localExpression i) z)
        (holRealDeriv (φ.localExpression i) z)).re := by
  have hp := trace_hessian_product (φ := ψ.localExpression i) (ψ := φ.localExpression i)
    ((ψ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz))
    ((φ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz))
    (g.matrix i z) (g.positive i z hz).isHermitian
  change ((g.laplacian (ψ.product φ)).localExpression i z -
    ψ.localExpression i z * (g.laplacian φ).localExpression i z -
    φ.localExpression i z * (g.laplacian ψ).localExpression i z) / 2 = _
  rw [g.laplacian_localExpression _ i hz, g.laplacian_localExpression _ i hz,
    g.laplacian_localExpression _ i hz]
  change (((g.matrix i z)⁻¹ * PotentialKaehler.potentialMatrix
      (fun y => ψ.localExpression i y * φ.localExpression i y) z).trace.re -
    ψ.localExpression i z * ((g.matrix i z)⁻¹ * φ.hessian i z).trace.re -
    φ.localExpression i z * ((g.matrix i z)⁻¹ * ψ.hessian i z).trace.re) / 2 = _
  rw [hp]
  change (_ - _ * ((g.matrix i z)⁻¹ * PotentialKaehler.potentialMatrix (φ.localExpression i) z).trace.re -
    _ * ((g.matrix i z)⁻¹ * PotentialKaehler.potentialMatrix (ψ.localExpression i) z).trace.re) / 2 = _
  ring

lemma energy_nonneg (g : KaehlerMetric A) (φ : SmoothRealFunction A) (x : X) :
    0 ≤ (g.energy φ φ).value x := by
  obtain ⟨i, hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have he := g.energy_local φ φ i hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi] at he
  rw [he]
  exact gradientPair_self_nonneg _ (g.positive i _ hz) _

lemma energy_symm (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A) :
    (g.energy ψ φ).value = (g.energy φ ψ).value := by
  funext x
  obtain ⟨i, hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have he := g.energy_local ψ φ i hz
  have he' := g.energy_local φ ψ i hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi] at he he'
  rw [he, he', ← gradientPair_star _ (g.positive i _ hz).isHermitian]
  rfl

lemma holRealDeriv_zero_of_notMem_tsupport (ψ : SmoothRealFunction A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target)
    (hs : (A.chart i).symm z ∉ tsupport ψ.value) : holRealDeriv (ψ.localExpression i) z = 0 := by
  have he : ψ.localExpression i =ᶠ[𝓝 z] (fun _ => 0) :=
    (notMem_tsupport_iff_eventuallyEq.mp hs).comp_tendsto
      (((A.chart i).continuousOn_symm z hz).continuousAt ((A.chart i).open_target.mem_nhds hz))
  funext j
  unfold holRealDeriv
  rw [he.fderiv_eq]
  simp only [fderiv_const_apply, map_zero, Pi.zero_apply]

lemma energy_support (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A) :
    tsupport (g.energy ψ φ).value ⊆ tsupport ψ.value := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hs
  obtain ⟨i, hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have he := g.energy_local ψ φ i hz
  have hd := holRealDeriv_zero_of_notMem_tsupport ψ i hz
    (by simpa only [(A.chart i).left_inv hi] using hs)
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi] at he
  dsimp only [SmoothRealFunction.localExpression] at hd
  rw [hd] at he
  simp only [gradientPair, Pi.zero_apply, star_zero, mul_zero, zero_mul, Finset.sum_const_zero,
    Complex.zero_re] at he
  exact hx he

lemma holRealDeriv_add {f h : Coordinates d → ℝ} {z : Coordinates d}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    holRealDeriv (fun y => f y + h y) z = holRealDeriv f z + holRealDeriv h z := by
  funext j
  unfold holRealDeriv
  rw [fderiv_fun_add hf hh, map_add]
  rfl

lemma gradientPair_add_left (H : Matrix (Fin d) (Fin d) ℂ) (p q r : Fin d → ℂ) :
    gradientPair H (p + q) r = gradientPair H p r + gradientPair H q r := by
  simp [gradientPair, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma energy_add_left (g : KaehlerMetric A) (ψ χ φ : SmoothRealFunction A) :
    (g.energy (ψ.addFunction χ) φ).value =
      fun x => (g.energy ψ φ).value x + (g.energy χ φ).value x := by
  funext x
  obtain ⟨i, hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have he := g.energy_local (ψ.addFunction χ) φ i hz
  have he₁ := g.energy_local ψ φ i hz
  have he₂ := g.energy_local χ φ i hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi] at he he₁ he₂
  rw [he, he₁, he₂]
  change (gradientPair _ (holRealDeriv (fun y => ψ.localExpression i y + χ.localExpression i y) _)
    _).re = _
  rw [holRealDeriv_add (f := ψ.localExpression i) (h := χ.localExpression i) (((ψ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt (by simp))
    (((χ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt (by simp)),
    gradientPair_add_left, Complex.add_re]
  rfl

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
