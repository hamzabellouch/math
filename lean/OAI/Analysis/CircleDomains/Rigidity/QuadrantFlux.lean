import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! Circle flux expressed on four quarter arcs. This representation
uses the same boundary values as the axial slice integrals. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def quadrantSign (s : Bool) : ℝ := if s then 1 else -1
 def quadrantNormal (s t : Bool) (θ : ℝ) : ℂ :=
    ⟨quadrantSign s*Real.cos θ,quadrantSign t*Real.sin θ⟩
 def quadrantPoint (c : ℂ) (r : ℝ) (s t : Bool) (θ : ℝ) : ℂ := c+r*quadrantNormal s t θ
 def quadrantFlux (F : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
    ∫ θ in (0 : ℝ)..(Real.pi/2),
      r*∑ s : Bool, ∑ t : Bool, (F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)).re

 theorem quadrantNormal_norm (s t : Bool) (θ : ℝ) : ‖quadrantNormal s t θ‖ = 1 := by
  have hn : ‖quadrantNormal s t θ‖^2 = 1 := by
    rw [Complex.sq_norm]
    have hc := Real.cos_sq_add_sin_sq θ
    cases s <;> cases t <;>
      norm_num [quadrantNormal,quadrantSign,Complex.normSq_apply] <;> nlinarith
  nlinarith [norm_nonneg (quadrantNormal s t θ)]

 theorem quadrantFlux_sub_const (F : ℂ → ℂ) (b c : ℂ) (r : ℝ) :
    quadrantFlux (fun z => F z-b) c r = quadrantFlux F c r := by
  unfold quadrantFlux
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [sub_mul,Complex.sub_re,Finset.sum_sub_distrib]
  have hz : (∑ s : Bool, ∑ t : Bool, (b*star (quadrantNormal s t θ)).re) = 0 := by
    simp [quadrantNormal,quadrantSign,Complex.mul_re]
    ring
  rw [hz,sub_zero]

 theorem quadrantFlux_abs_le {F : ℂ → ℂ} {c : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (_hε : 0 ≤ ε)
    (hb : ∀ s t θ, θ ∈ Icc (0 : ℝ) (Real.pi/2) → ‖F (quadrantPoint c r s t θ)‖ ≤ ε) :
    |quadrantFlux F c r| ≤ 2*Real.pi*r*ε := by
  have hπ : 0 ≤ Real.pi/2 := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun θ => r*∑ s : Bool, ∑ t : Bool, (F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)).re)
    (a := (0 : ℝ)) (b := Real.pi/2) (C := r*(4*ε)) (fun θ hθ => by
      rw [uIoc_of_le hπ] at hθ
      have hθ' : θ ∈ Icc (0 : ℝ) (Real.pi/2) := ⟨hθ.1.le,hθ.2⟩
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hr]
      apply mul_le_mul_of_nonneg_left _ hr
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ s : Bool, ∑ t : Bool, ε := by
          apply Finset.sum_le_sum
          intro s _
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          apply Finset.sum_le_sum
          intro t _
          exact (Complex.abs_re_le_norm _).trans ((by
            rw [norm_mul,norm_star,quadrantNormal_norm,mul_one]
            exact hb s t θ hθ') : ‖F (quadrantPoint c r s t θ)*star (quadrantNormal s t θ)‖ ≤ ε)
        _ = 4*ε := by simp; ring)
  change ‖quadrantFlux F c r‖ ≤ _ at h
  rw [Real.norm_eq_abs,sub_zero,abs_of_nonneg hπ] at h
  exact h.trans_eq (by ring)

 theorem quadrantFlux_near_const {F : ℂ → ℂ} {b c : ℂ} {r ε : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hb : ∀ s t θ, θ ∈ Icc (0 : ℝ) (Real.pi/2) → ‖F (quadrantPoint c r s t θ)-b‖ ≤ ε) :
    |quadrantFlux F c r| ≤ 2*Real.pi*r*ε := by
  rw [← quadrantFlux_sub_const F b]
  exact quadrantFlux_abs_le hr hε hb

end CircleDomainRigidity

end

end OAI
