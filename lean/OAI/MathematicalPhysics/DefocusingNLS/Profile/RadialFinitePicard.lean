import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFiniteIntegral
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! An exponentially weighted Picard map for the finite exterior continuation interval. -/

open Set
namespace DefocusingNLS

noncomputable def radialFiniteTimeWeight (T η : ℝ)
    (u : C(Icc (0 : ℝ) T, ℂ × ℂ)) : C(Icc (0 : ℝ) T, ℂ × ℂ) where
  toFun t := Real.exp (η*t) • u t
  continuous_toFun :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul u.continuous

theorem radialFiniteTimeWeight_cancel (T η : ℝ)
    (u : C(Icc (0 : ℝ) T, ℂ × ℂ)) :
    radialFiniteTimeWeight T η (radialFiniteTimeWeight T (-η) u)=u := by
  apply ContinuousMap.ext
  intro t
  change Real.exp (η*(t : ℝ)) • (Real.exp (-η*(t : ℝ)) • u t)=u t
  rw [smul_smul,← Real.exp_add,show η*(t : ℝ)+ -η*(t : ℝ)=0 by ring,Real.exp_zero,one_smul]

noncomputable def radialFiniteHistory (T η : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × (ℂ × ℂ), ℂ × ℂ))
    (u : C(Icc (0 : ℝ) T, ℂ × ℂ)) (s : ℝ) : ℂ × ℂ :=
  F (projIcc 0 T hT s,radialFiniteTimeWeight T η u (projIcc 0 T hT s))

theorem radialFiniteHistory_continuous (T η : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × (ℂ × ℂ), ℂ × ℂ))
    (u : C(Icc (0 : ℝ) T, ℂ × ℂ)) : Continuous (radialFiniteHistory T η hT F u) := by
  exact F.continuous.comp (continuous_projIcc.prodMk
    ((radialFiniteTimeWeight T η u).continuous.comp continuous_projIcc))

noncomputable def radialFinitePicard (T η : ℝ) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × (ℂ × ℂ), ℂ × ℂ)) (x₀ : ℂ × ℂ)
    (u : C(Icc (0 : ℝ) T, ℂ × ℂ)) : C(Icc (0 : ℝ) T, ℂ × ℂ) where
  toFun t := Real.exp (-η*t) • (x₀+∫ s in 0..(t : ℝ), radialFiniteHistory T η hT F u s)
  continuous_toFun := by
    have hi : Continuous (fun r : ℝ => ∫ s in 0..r, radialFiniteHistory T η hT F u s) :=
      (show Differentiable ℝ (fun r : ℝ => ∫ s in 0..r, radialFiniteHistory T η hT F u s) from
        fun r => (radial_finite_integral_hasDerivAt _ (radialFiniteHistory_continuous T η hT F u) r).differentiableAt).continuous
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      (continuous_const.add (hi.comp continuous_subtype_val))

theorem radialFinitePicard_dist (T η K : ℝ) (hT : 0 ≤ T) (hη : 0 < η) (hK : 0 ≤ K)
    (F : C((Icc (0 : ℝ) T) × (ℂ × ℂ), ℂ × ℂ)) (x₀ : ℂ × ℂ)
    (hF : ∀ t x y, ‖F (t,x)-F (t,y)‖ ≤ K*‖x-y‖)
    (u v : C(Icc (0 : ℝ) T, ℂ × ℂ)) :
    dist (radialFinitePicard T η hT F x₀ u) (radialFinitePicard T η hT F x₀ v) ≤
      K/η*dist u v := by
  apply (ContinuousMap.dist_le (mul_nonneg (div_nonneg hK hη.le) dist_nonneg)).mpr
  intro t
  have hb : ∀ s ∈ Icc 0 (t : ℝ),
      ‖radialFiniteHistory T η hT F u s-radialFiniteHistory T η hT F v s‖ ≤
        (K*dist u v)*Real.exp (η*s) := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans t.2.2⟩
    simp only [radialFiniteHistory,projIcc_of_mem hT hsT]
    apply (hF _ _ _).trans
    change K*‖Real.exp (η*s) • u ⟨s,hsT⟩-Real.exp (η*s) • v ⟨s,hsT⟩‖ ≤ _
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have hu := ContinuousMap.dist_apply_le_dist (f := u) (g := v) ⟨s,hsT⟩
    rw [dist_eq_norm] at hu
    calc
      _ ≤ K*(Real.exp (η*s)*dist u v) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hu (Real.exp_nonneg _)) hK
      _ = _ := by ring
  have hi := radial_finite_integral_weighted η t (K*dist u v) hη t.2.1
    (mul_nonneg hK dist_nonneg)
    (fun s => radialFiniteHistory T η hT F u s-radialFiniteHistory T η hT F v s) hb
  change dist (Real.exp (-η*(t : ℝ)) •
    (x₀+∫ s in 0..(t : ℝ), radialFiniteHistory T η hT F u s))
    (Real.exp (-η*(t : ℝ)) •
    (x₀+∫ s in 0..(t : ℝ), radialFiniteHistory T η hT F v s)) ≤ _
  rw [dist_eq_norm,← smul_sub,add_sub_add_left_eq_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← intervalIntegral.integral_sub
      ((radialFiniteHistory_continuous T η hT F u).intervalIntegrable 0 t)
      ((radialFiniteHistory_continuous T η hT F v).intervalIntegrable 0 t)]
  exact hi.trans_eq (by ring)

end DefocusingNLS

end OAI
