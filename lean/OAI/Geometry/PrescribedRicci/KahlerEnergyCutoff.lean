import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedRicci.KahlerEnergyProduct
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy

namespace OAI

/-! Kahler Energy Cutoff. -/

section

 

noncomputable section
open Matrix Set Filter Topology MeasureTheory
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

omit [T2Space X] in
lemma cutoff_energy_bound (g : KaehlerMetric A) (ρ : SmoothRealFunction A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : SmoothRealFunction A) (x : X),
      (g.energy (ρ.product φ) (ρ.product φ)).value x ≤
        C * ((g.energy φ φ).value x + φ.value x ^ 2) := by
  let F : C(X,ℝ) := ⟨ρ.value,ρ.continuous⟩
  let E : C(X,ℝ) := ⟨(g.energy ρ ρ).value,(g.energy ρ ρ).continuous⟩
  let C : ℝ := 2*(‖F‖^2+‖E‖+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun φ x => ?_⟩
  have hF : ρ.value x ^ 2 ≤ ‖F‖^2 := by
    have hh := F.norm_coe_le_norm x
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hh
    simpa only [Real.norm_eq_abs, sq_abs, F, ContinuousMap.coe_mk] using hs
  have hE : (g.energy ρ ρ).value x ≤ ‖E‖ := by
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, E, ContinuousMap.coe_mk] using E.norm_coe_le_norm x)
  have hcoefF : 2*ρ.value x^2 ≤ C := by dsimp [C]; nlinarith [norm_nonneg E]
  have hcoefE : 2*(g.energy ρ ρ).value x ≤ C := by dsimp [C]; nlinarith [sq_nonneg ‖F‖]
  calc
    _ ≤ 2*ρ.value x^2*(g.energy φ φ).value x + 2*φ.value x^2*(g.energy ρ ρ).value x :=
      g.energy_product_le ρ φ x
    _ = (2*ρ.value x^2)*(g.energy φ φ).value x + (2*(g.energy ρ ρ).value x)*φ.value x^2 := by ring
    _ ≤ C*(g.energy φ φ).value x + C*φ.value x^2 :=
      add_le_add (mul_le_mul_of_nonneg_right hcoefF (g.energy_nonneg φ x))
        (mul_le_mul_of_nonneg_right hcoefE (sq_nonneg _))
    _ = _ := by ring

lemma cutoff_integral_energy_bound (g : KaehlerMetric A) (ρ : SmoothRealFunction A) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : SmoothRealFunction A,
      g.integral (g.energy (ρ.product φ) (ρ.product φ)).value ≤
        C * (g.integral (g.energy φ φ).value + g.integral (fun x => φ.value x^2)) := by
  obtain ⟨C,hC,hbound⟩ := g.cutoff_energy_bound ρ
  refine ⟨C,hC,fun φ => ?_⟩
  have hh := g.integral_mono (g.energy (ρ.product φ) (ρ.product φ)).continuous
    (continuous_const.fun_mul ((g.energy φ φ).continuous.fun_add (φ.continuous.pow 2))) (hbound φ)
  rwa [g.integral_const_mul, g.integral_add (g.energy φ φ).continuous (φ.continuous.pow 2)] at hh

omit [T2Space X] [CompactSpace X] in
lemma product_support_left (ρ φ : SmoothRealFunction A) :
    tsupport (ρ.product φ).value ⊆ tsupport ρ.value := by
  apply closure_minimal _ (isClosed_tsupport _)
  exact (Function.support_mul_subset_left _ _).trans subset_closure

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
