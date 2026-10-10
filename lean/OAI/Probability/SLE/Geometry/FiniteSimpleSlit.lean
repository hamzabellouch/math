import OAI.Probability.SLE.Geometry.SimpleArcComplement

namespace OAI

/-! The finite trace of a simple interior slit has no swallowed points
away from the slit itself. -/
noncomputable section
open Set Filter Function
open scoped Topology NNReal

namespace SLEExactGauge

theorem finite_simple_slit_free
    (γ : ℝ≥0 → ℂ) (hc : Continuous γ) (h0 : γ 0=0)
    (T : ℝ≥0) (hT : 0 < T) (hi : InjOn γ (Icc 0 T))
    (hH : ∀ t ∈ Ioc 0 T, γ t ∈ upperHalfPlane) :
    upperHalfPlane \ (γ '' Icc 0 T) ⊆ survivingDomain γ T := by
  let v (u : unitInterval) : ℝ≥0 := ⟨u,u.property.1⟩
  have hv : Continuous v := continuous_subtype_val.subtype_mk _
  let p : C(unitInterval,ℂ) := ⟨fun u => γ (T*v u),hc.comp (continuous_const.mul hv)⟩
  have hv1 (u : unitInterval) : v u ≤ 1 := u.property.2
  have ht (u : unitInterval) : T*v u ∈ Icc 0 T :=
    ⟨zero_le,by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hv1 u) zero_le⟩
  have hp : Injective p := by
    intro u w he
    have heq := hi (ht u) (ht w) he
    have heq' := mul_left_cancel₀ hT.ne' heq
    apply Subtype.ext
    exact congrArg (fun x : ℝ≥0 => (x : ℝ)) heq'
  have hv0 : v 0=0 := Subtype.ext rfl
  have hp0 : p 0=0 := by change γ (T*v 0)=0; rw [hv0,mul_zero,h0]
  have hpH (u : unitInterval) (hu : u ≠ 0) : p u ∈ upperHalfPlane := by
    apply hH _ ⟨mul_pos hT ?_,(ht u).2⟩
    change 0 < (u : ℝ)
    exact lt_of_le_of_ne u.property.1 (fun he => hu (Subtype.ext he.symm))
  have hrange : range p=γ '' Icc 0 T := by
    apply Subset.antisymm
    · rintro _ ⟨u,rfl⟩
      exact ⟨T*v u,ht u,rfl⟩
    · rintro _ ⟨t,ht',rfl⟩
      let u : unitInterval := ⟨(t/T : ℝ≥0),
        (t/T).coe_nonneg,by exact_mod_cast (div_le_one hT).mpr ht'.2⟩
      refine ⟨u,?_⟩
      change γ (T*v u)=γ t
      congr 1
      change T*(t/T)=t
      exact mul_div_cancel₀ _ hT.ne'
  intro z hz
  refine ⟨hz,?_⟩
  rw [← hrange]
  exact simple_arc_halfPlane_component_unbounded p hp hp0 hpH (hrange.symm ▸ hz)

end SLEExactGauge

end

end OAI
