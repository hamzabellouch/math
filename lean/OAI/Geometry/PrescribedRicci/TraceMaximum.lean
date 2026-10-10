import Mathlib
import OAI.Geometry.PrescribedRicci.KaehlerLogTrace
import OAI.Geometry.PrescribedRicci.KaehlerTrace
import OAI.Geometry.PrescribedRicci.MongeAmpereC0
import OAI.Geometry.PrescribedRicci.UniformChernLu
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Trace Maximum. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder MatrixOrder
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma laplacian_addFunction (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A) (x : X) :
    (g.laplacian (φ.addFunction ψ)).value x = (g.laplacian φ).value x+(g.laplacian ψ).value x := by
  obtain ⟨q,hq⟩ := A.covers x
  change g.laplacianValue _ x = g.laplacianValue _ x+g.laplacianValue _ x
  rw [g.laplacianValue_local _ q hq,g.laplacianValue_local φ q hq,g.laplacianValue_local ψ q hq]
  simp only [linearizedMongeAmpere,φ.hessian_addFunction ψ q ((A.chart q).mapsTo hq),
    mul_add,trace_add,Complex.add_re]

lemma laplacian_realSMul (g : KaehlerMetric A) (φ : SmoothRealFunction A) (c : ℝ) (x : X) :
    (g.laplacian (φ.realSMul c)).value x = c*(g.laplacian φ).value x :=
  g.linearizedMongeAmpere_realSMul φ c _ _

lemma laplacian_nonpos_at_globalMax (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    {x : X} (hx : ∀ y, φ.value y ≤ φ.value x) : (g.laplacian φ).value x ≤ 0 :=
  g.linearized_nonpos_at_globalMax φ hx _ (A.covers x).choose_spec

variable [CompactSpace X] [Nonempty X]

lemma trace_bound_of_C0_chernLu (g : KaehlerMetric A) (hd : 0 < d)
    (φ : SmoothRealFunction A) (hp : g.PositivePotential φ) {C B : ℝ}
    (hC : 0 ≤ C) (hB : ∀ x, |φ.value x| ≤ B)
    (hLu : ∀ x, -C*((g.deform φ hp).traceMetric g).value x ≤
      ((g.deform φ hp).laplacian ((g.deform φ hp).logTrace g hd)).value x) :
    ∀ x, ((g.deform φ hp).traceMetric g).value x ≤
      ((C+1)*(d:ℝ))*Real.exp (2*(C+1)*B) := by
  let h := g.deform φ hp
  let f := (h.logTrace g hd).addFunction (φ.realSMul (-(C+1)))
  obtain ⟨x₀,_,hm⟩ := isCompact_univ.exists_isMaxOn univ_nonempty f.continuous.continuousOn
  have hmax : ∀ y, f.value y ≤ f.value x₀ := fun y => hm (mem_univ y)
  have hlap := h.laplacian_nonpos_at_globalMax f hmax
  rw [laplacian_addFunction,laplacian_realSMul,g.laplacian_deform φ hp] at hlap
  have hS₀ : (h.traceMetric g).value x₀ ≤ (C+1)*(d:ℝ) := by
    have hh := hLu x₀
    change -C*(h.traceMetric g).value x₀ ≤ _ at hh
    nlinarith
  intro x
  have hlog : Real.log ((h.traceMetric g).value x) ≤
      Real.log ((h.traceMetric g).value x₀)+2*(C+1)*B := by
    have hh := hmax x
    change Real.log ((h.traceMetric g).value x)+(-(C+1))*φ.value x ≤
      Real.log ((h.traceMetric g).value x₀)+(-(C+1))*φ.value x₀ at hh
    have hx := abs_le.mp (hB x)
    have hy := abs_le.mp (hB x₀)
    nlinarith [mul_nonneg (by linarith : 0 ≤ C+1) (sub_nonneg.mpr hx.2),
      mul_nonneg (by linarith : 0 ≤ C+1) (by linarith : 0 ≤ φ.value x₀+B)]
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add,Real.exp_log (h.traceMetric_pos g hd x),
    Real.exp_log (h.traceMetric_pos g hd x₀)] at he
  exact he.trans (mul_le_mul_of_nonneg_right hS₀ (Real.exp_pos _).le)

variable [T2Space X] [ConnectedSpace X]

 

theorem volumePath_trace_bound (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    (hd : 2 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ), g.integral φ.value = 0 →
    ∀ (t b : ℝ), t ∈ Icc (0:ℝ) 1 →
    (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
    ∀ x, ((g.deform φ hp).traceMetric g).value x ≤ K := by
  have hd' : 0 < d := by omega
  obtain ⟨C,hC,hLu⟩ := g.uniform_chernLu line hd'
  obtain ⟨B,hB,hC0⟩ := g.volumePath_C0_bound line hd
  refine ⟨((C+1)*(d:ℝ))*Real.exp (2*(C+1)*B),by positivity,?_⟩
  intro φ hp hm t b ht heq
  exact g.trace_bound_of_C0_chernLu hd' φ hp hC (hC0 φ hp hm t b ht heq)
    (hLu t b φ hp heq ht)

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
