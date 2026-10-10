import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExtendedTail

namespace OAI

/-! Continue the H-convergent nonlinear family without losing its outgoing class. -/

open Set Filter
namespace DefocusingNLS

theorem exists_radialExterior_outgoing_extended (ν m : ℕ → ℂ) (q m₀ : ℂ)
    (hq : -1 < q.re) (hν : Tendsto ν atTop (nhds (-2*q)))
    (hm : Tendsto m atTop (nhds m₀)) (δ ρ l : ℝ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) (hρ : ρ < 1)
    (hupper : ∀ t, l ≤ t → ‖(radialFreeSlowJet q m₀ t).1‖+2*δ ≤ ρ)
    (hlower : ∀ t, l ≤ t → δ < ‖(radialFreeSlowJet q m₀ t).1‖) :
    ∃ Z : ℕ → ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z (radialFreeSlowJet q m₀) atTop (Ici l) ∧
      (∀ n, Continuous (Z n)) ∧
      (∀ᶠ n in atTop, HasRadialOutgoingExpansion (ν n) n (m n) (Z n)) ∧
      ∀ᶠ n in atTop, ∀ t, l ≤ t → (Z n t).1 ≠ 0 ∧
        HasDerivAt (Z n) (radialExteriorODEField (ν n) n t (Z n t)) t := by
  obtain ⟨S,_,Y,hYconv,hYc,hYout,hY⟩ :=
    exists_radialExterior_outgoing_H_limit ν m q m₀ hq hν hm δ hδ hδm hsmall
  let U := max S l
  have hSU : S ≤ U := le_max_left _ _
  have hlU : l ≤ U := le_max_right _ _
  have hgc : Continuous (radialFreeSlowJet q m₀) :=
    (show Differentiable ℝ (radialFreeSlowJet q m₀) from
      fun t => (radialFreeSlowJet_hasDerivAt q m₀ hq t).differentiableAt).continuous
  obtain ⟨X,hX,hXconv,hXactual⟩ := exists_radialExterior_finite_limit ν (-2*q) hν
    (radialFreeSlowJet q m₀) hgc δ ρ U (U-l) hδ (sub_nonneg.mpr hlU) hρ
    (fun t ht => hupper t (by linarith [ht.1]))
    (fun t ht => hlower t (by linarith [ht.1]))
    (fun t _ => radialFreeSlowJet_hasDerivAt q m₀ hq t)
    (fun n => Y n U) (hYconv.tendsto_at hSU)
  let Z : ℕ → ℝ → ℂ × ℂ := fun n => radialExteriorSplice U (X n) (Y n)
  have hXconv' : TendstoUniformlyOn X (radialFreeSlowJet q m₀) atTop (Icc l U) := by
    simpa only [sub_sub_cancel] using hXconv
  refine ⟨Z,radialExteriorSplice_uniform_limit l U X Y _ hXconv'
    (hYconv.mono (fun t ht => hSU.trans ht)),?_,?_,?_⟩
  · intro n
    exact radialExteriorSplice_continuous U (X n) (Y n) (hX n).1 (hYc n) (hX n).2
  · filter_upwards [hYout] with n hn
    apply hn.congr
    filter_upwards [eventually_gt_atTop U] with t ht
    simp only [Z,radialExteriorSplice,not_le.mpr ht,ite_false]
  · filter_upwards [hY,hXactual] with n hnY hnX t ht
    have hnn : (Z n t).1 ≠ 0 := by
      by_cases h : t ≤ U
      · simpa only [Z,radialExteriorSplice,ite_eq_left h] using
          (hnX t ⟨by linarith,h⟩).1
      · simpa only [Z,radialExteriorSplice,ite_eq_right h] using
          (hnY t (hSU.trans (not_le.mp h).le)).1
    refine ⟨hnn,?_⟩
    apply radialExteriorSplice_hasDerivAt U t (X n) (Y n) (radialExteriorODEField (ν n) n)
    · intro h
      exact (hnX t ⟨by linarith,h⟩).2
    · intro h
      exact (hnY t (hSU.trans h)).2
    · exact (hX n).2

end DefocusingNLS

end OAI
