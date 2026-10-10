import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinBounds

namespace OAI

/-! Properness of the actual arithmetic height denominator. Every point
has a maximal-height representative for the principal group. This is the
first reduction step for the global automorphic domain. -/
noncomputable section
open Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaBottomRow_height_superlevel_finite {p : ℂ × ℝ} (hp : 0<p.2)
    {a : ℝ} (ha : 0<a) :
    Set.Finite {r : CubicThetaBottomRow | a ≤ r.height p} := by
  let B := p.2*cubicThetaHeightConstant p/a
  have hfin : Set.Finite {r : CubicThetaBottomRow | norm r.c ≤ B ∧ norm r.d ≤ B} := by
    have hi : Function.Injective (fun r : CubicThetaBottomRow => (r.c,r.d)) := by
      intro r t he
      exact CubicThetaBottomRow.ext (Prod.mk.inj he).1 (Prod.mk.inj he).2
    exact ((finite_norm_le B).prod (finite_norm_le B)).preimage hi.injOn
  apply hfin.subset
  intro r hr
  have hN : 0<1+norm r.c+norm r.d := by linarith [norm_nonneg r.c,norm_nonneg r.d]
  have hmul : a*(1+norm r.c+norm r.d) ≤ p.2*cubicThetaHeightConstant p :=
    (le_div_iff₀ hN).mp (hr.trans (r.height_le hp))
  have hbound : 1+norm r.c+norm r.d ≤ B := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  exact ⟨by linarith [norm_nonneg r.d],by linarith [norm_nonneg r.c]⟩

theorem cubicThetaBottomRow_exists_max_height {p : ℂ × ℝ} (hp : 0<p.2) :
    ∃ r : CubicThetaBottomRow, ∀ t : CubicThetaBottomRow, t.height p ≤ r.height p := by
  let r0 := cubicThetaBottomRow (1 : cubicThetaPrincipalGroup)
  let S : Set CubicThetaBottomRow := {r | r0.height p ≤ r.height p}
  have hfin : S.Finite := cubicThetaBottomRow_height_superlevel_finite hp (r0.height_pos hp)
  have hne : hfin.toFinset.Nonempty := ⟨r0,by simp [S]⟩
  obtain ⟨r,hr,hmax⟩ := hfin.toFinset.exists_max_image (fun r => r.height p) hne
  refine ⟨r,?_⟩
  intro t
  by_cases ht : r0.height p ≤ t.height p
  · exact hmax t (by simpa [S] using ht)
  · exact (lt_of_not_ge ht).le.trans (by simpa [S] using hr)

end CubicFirstMoment

end

end OAI
