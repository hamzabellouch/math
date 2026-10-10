import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCommonTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorHIdentification

namespace OAI

/-! The nonlinear exterior family converges to the actual outgoing H profile. -/

open Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialExterior_H_limit (ν m : ℕ → ℂ) (q m₀ : ℂ)
    (hq : -1 < q.re) (hν : Tendsto ν atTop (nhds (-2*q)))
    (hm : Tendsto m atTop (nhds m₀)) (δ : ℝ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∃ Z : ℕ → ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z (radialFreeSlowJet q m₀) atTop (Ici S) ∧
      (∀ n, Tendsto (Z n) atTop (nhds (m n,0))) ∧
      Tendsto (radialFreeSlowJet q m₀) atTop (nhds (m₀,0)) ∧
      ∀ᶠ n in atTop, ∀ t, S ≤ t →
        (Z n t).1 ≠ 0 ∧ HasDerivAt (fun s => (Z n s).1) (Z n t).2 t ∧
        HasDerivAt (fun s => (Z n s).2)
          (-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  obtain ⟨T,hT,Z,Z₀,hconv,hlim,hlim₀,⟨j,w,hκ,heq⟩,hfree,hactual⟩ :=
    exists_radialExterior_common_tail_with_expansion ν m (-2*q) m₀ hν hm δ hδ hδm hsmall
  have hj : j ≠ 0 := by
    intro hj
    rw [hj,Nat.cast_zero,mul_zero] at hκ
    exact (not_lt_of_ge (radialExteriorMatrixBound_pos (-2*q)).le) hκ
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  let S := max T (max 0 (Real.log 4/2))
  have hident : ∀ t, S ≤ t → Z₀ t=radialFreeSlowJet q m₀ t := by
    intro t ht
    rw [heq]
    apply radialExterior_free_correction_eq_H q m₀ hq k T w hκ ?_ t ht
    intro r hr
    have hh := (hfree r hr).1.prodMk (hfree r hr).2
    rw [heq] at hh
    apply hh.congr_deriv
    apply Prod.ext
    · simp [radialExteriorErrorMatrix]
    · simp only [radialExteriorErrorMatrix,ContinuousLinearMap.prod_apply,
        neg_apply,add_apply,
        smul_apply,ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',smul_eq_mul,Prod.snd_add]
      ring
  have hS : 0 ≤ S := hT.trans (le_max_left _ _)
  refine ⟨S,hS,Z,?_,hlim,?_,?_⟩
  · exact (hconv.mono (fun t ht => hS.trans ht)).congr_right (fun t ht => hident t ht)
  · apply hlim₀.congr'
    filter_upwards [eventually_ge_atTop S] with t ht
    exact hident t ht
  · filter_upwards [hactual] with n hn t ht
    exact hn t ((le_max_left T _).trans ht)

end DefocusingNLS

end OAI
