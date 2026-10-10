import OAI.Geometry.SurfaceImmersion.Whitney.UnorderedSurfacePairs

namespace OAI

/-! The two sides of a line become a half-line after forgetting their
ordering. This is the endpoint coordinate for a prepared crosscap. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def unorderedLinePair (a w : Base) (t : ℝ) : UnorderedSurfacePairs Base :=
  unorderedPair (a+t • w,a-t • w)

lemma unorderedLinePair_continuous (a w : Base) : Continuous (unorderedLinePair a w) := by
  apply unorderedPair_continuous.comp
  exact (continuous_const.add (continuous_id.smul continuous_const)).prodMk
    (continuous_const.sub (continuous_id.smul continuous_const))

lemma unorderedLinePair_eq_iff (a w : Base) (hw : w ≠ 0) (s t : ℝ) :
    unorderedLinePair a w s = unorderedLinePair a w t ↔ s = t ∨ s = -t := by
  constructor
  · intro h
    rcases unorderedPair_eq.mp h with h | h
    · apply Or.inl
      have he := congrArg Prod.fst h
      have hs : (s-t) • w = 0 := by
        rw [sub_smul,sub_eq_zero]
        exact add_left_cancel he
      exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hw)
    · apply Or.inr
      have he := congrArg Prod.fst h
      have hs : (s+t) • w = 0 := by
        calc
          _ = (a+s • w)-(a-t • w) := by module
          _ = 0 := sub_eq_zero.mpr he
      exact eq_neg_iff_add_eq_zero.mpr ((smul_eq_zero.mp hs).resolve_right hw)
  · rintro (rfl | rfl)
    · rfl
    · apply unorderedPair_eq.mpr
      right
      apply Prod.ext <;> simp only [Prod.swap_prod_mk,neg_smul,sub_eq_add_neg,neg_neg]

lemma unorderedLinePair_injOn_nonneg (a w : Base) (hw : w ≠ 0) :
    (Ici (0 : ℝ)).InjOn (unorderedLinePair a w) := by
  intro s hs t ht he
  rcases (unorderedLinePair_eq_iff a w hw s t).mp he with h | h
  · exact h
  · change 0 ≤ s at hs
    change 0 ≤ t at ht
    have : s = 0 ∧ t = 0 := by constructor <;> linarith
    exact this.1.trans this.2.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
