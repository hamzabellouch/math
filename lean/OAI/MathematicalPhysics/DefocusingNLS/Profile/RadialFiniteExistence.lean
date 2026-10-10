import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFinitePicard

namespace OAI

/-! Existence on every finite interval for the globally clipped exterior ODE. -/

open Set
namespace DefocusingNLS

theorem exists_radial_finite_solution (T : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × (ℂ × ℂ), ℂ × ℂ))
    (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ t x y, ‖F (t,x)-F (t,y)‖ ≤ K*‖x-y‖) (x₀ : ℂ × ℂ) :
    ∃ α : ℝ → ℂ × ℂ, Continuous α ∧ α 0=x₀ ∧
      ∀ t (ht : t ∈ Icc 0 T), HasDerivAt α (F (⟨t,ht⟩,α t)) t := by
  let η := K+1
  have hη : 0 < η := by dsimp [η]; linarith
  have hratio : 0 ≤ K/η := div_nonneg hK hη.le
  have hlt : K/η < 1 := (div_lt_one hη).mpr (by dsimp [η]; linarith)
  let P := radialFinitePicard T η hT F x₀
  have hP : ContractingWith ⟨K/η,hratio⟩ P :=
    ⟨hlt,LipschitzWith.of_dist_le_mul (radialFinitePicard_dist T η K hT hη hK F x₀ hF)⟩
  let v := hP.fixedPoint P
  have hv : P v=v := hP.fixedPoint_isFixedPt
  let α : ℝ → ℂ × ℂ := fun t => x₀+∫ s in 0..t, radialFiniteHistory T η hT F v s
  have hαd (t : ℝ) : HasDerivAt α (radialFiniteHistory T η hT F v t) t :=
    (radial_finite_integral_hasDerivAt _ (radialFiniteHistory_continuous T η hT F v) t).const_add x₀
  have hα (t : Icc (0 : ℝ) T) : α t=radialFiniteTimeWeight T η v t := by
    have h := congrArg (fun f : C(Icc (0 : ℝ) T, ℂ × ℂ) => Real.exp (η*(t : ℝ)) • f t) hv
    change Real.exp (η*(t : ℝ)) • (Real.exp (-η*(t : ℝ)) • α t)=radialFiniteTimeWeight T η v t at h
    rw [smul_smul,← Real.exp_add,show η*(t : ℝ)+ -η*(t : ℝ)=0 by ring,Real.exp_zero,one_smul] at h
    exact h
  refine ⟨α,(show Differentiable ℝ α from fun t => (hαd t).differentiableAt).continuous,?_,?_⟩
  · simp [α]
  · intro t ht
    apply (hαd t).congr_deriv
    simp only [radialFiniteHistory,projIcc_of_mem hT ht]
    rw [← hα ⟨t,ht⟩]

end DefocusingNLS

end OAI
