import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorHLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoing

namespace OAI

/-! The H limit retains the nonlinear outgoing expansion and continuity data. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialExterior_outgoing_H_limit (ν m : ℕ → ℂ) (q m₀ : ℂ)
    (hq : -1 < q.re) (hν : Tendsto ν atTop (nhds (-2*q)))
    (hm : Tendsto m atTop (nhds m₀)) (δ : ℝ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∃ Z : ℕ → ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z (radialFreeSlowJet q m₀) atTop (Ici S) ∧
      (∀ n, Continuous (Z n)) ∧
      (∀ᶠ n in atTop, HasRadialOutgoingExpansion (ν n) n (m n) (Z n)) ∧
      ∀ᶠ n in atTop, ∀ t, S ≤ t → (Z n t).1 ≠ 0 ∧
        HasDerivAt (Z n) (radialExteriorODEField (ν n) n t (Z n t)) t := by
  obtain ⟨T,hT,Z,Z₀,hconv,_,_,⟨j,w,hκ,heq⟩,⟨k,v,hrep,hmargin⟩,hfree,hactual⟩ :=
    exists_radialExterior_common_tail_data ν m (-2*q) m₀ hν hm δ hδ hδm hsmall
  have hj : j ≠ 0 := by
    intro hj
    rw [hj,Nat.cast_zero,mul_zero] at hκ
    exact (not_lt_of_ge (radialExteriorMatrixBound_pos (-2*q)).le) hκ
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  let S := max T (max 0 (Real.log 4/2))
  have hident : ∀ t, S ≤ t → Z₀ t=radialFreeSlowJet q m₀ t := by
    intro t ht
    rw [heq]
    apply radialExterior_free_correction_eq_H q m₀ hq j T w hκ ?_ t ht
    intro r hr
    have hh := (hfree r hr).1.prodMk (hfree r hr).2
    rw [heq] at hh
    apply hh.congr_deriv
    apply Prod.ext
    · simp [radialExteriorErrorMatrix]
    · simp only [radialExteriorErrorMatrix,ContinuousLinearMap.prod_apply,
        neg_apply,add_apply,smul_apply,ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',smul_eq_mul,Prod.snd_add]
      ring
  have hS : 0 ≤ S := hT.trans (le_max_left _ _)
  refine ⟨S,hS,Z,?_,?_,?_,?_⟩
  · exact (hconv.mono (fun t ht => hS.trans ht)).congr_right (fun t ht => hident t ht)
  · intro n
    rw [hrep n]
    exact continuous_radialExterior_polynomialCorrection _ _ _
  · filter_upwards [hmargin,(tendsto_iff_norm_sub_tendsto_zero.mp hm).eventually
      (gt_mem_nhds hδ)] with n hn hmn
    refine ⟨k,v n,0,?_,fun t _ => congrFun (hrep n) t⟩
    have hmnorm : ‖m n‖ ≤ ‖m₀‖+2*δ := by
      have ht := norm_le_norm_sub_add (m n) m₀
      linarith
    apply lt_of_le_of_lt _ hn
    apply add_le_add le_rfl
    calc
      _ ≤ (2*(n : ℝ)+1)*(‖m₀‖+2*δ)^(2*n) := by
        gcongr
      _ ≤ radialExteriorCutoffRate n m₀ δ := by
        unfold radialExteriorCutoffRate
        have hpos : 0 ≤ (2*(n : ℝ)+1)*(‖m₀‖+2*δ)^(2*n) := by positivity
        nlinarith
  · filter_upwards [hactual] with n hn t ht
    exact ⟨(hn t ((le_max_left T _).trans ht)).1,
      (hn t ((le_max_left T _).trans ht)).2.1.prodMk
        (hn t ((le_max_left T _).trans ht)).2.2⟩

end DefocusingNLS

end OAI
