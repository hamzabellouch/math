import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactCoreCover

namespace OAI

/-! Uniform arithmetic row bounds for transformations between two
compact positive-height charts. These bounds give local finiteness of
the actual arithmetic action. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

private def heightControl (p : ℂ × ℝ) : ℝ :=
  (2+(1+2*Complex.normSq p.1)/p.2^2)*p.2

private lemma heightControl_continuousOn {K : Set (ℂ × ℝ)}
    (hK : ∀ p∈K, 0<p.2) : ContinuousOn heightControl K := by
  intro p hp
  unfold heightControl
  fun_prop (disch := exact pow_ne_zero _ (hK p hp).ne')

private lemma inverseHeight_continuousOn {K : Set (ℂ × ℝ)}
    (hK : ∀ p∈K, 0<p.2) : ContinuousOn (fun p : ℂ × ℝ => 1/p.2) K := by
  intro p hp
  exact (continuousAt_const.div continuous_snd.continuousAt (hK p hp).ne').continuousWithinAt

lemma cubicThetaCompact_bottomRow_bound {K L : Set (ℂ × ℝ)}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKpos : ∀ p∈K, 0<p.2) (hLpos : ∀ p∈L, 0<p.2) :
    ∃ B : ℝ, ∀ g : SL(2,Eisenstein), ∀ p∈K,
      cubicThetaMobius (cubicThetaFullComplex g) p∈L → norm (g 1 0)+norm (g 1 1) ≤ B := by
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (heightControl_continuousOn hKpos)
  obtain ⟨B,hB⟩ := hL.exists_bound_of_continuousOn (inverseHeight_continuousOn hLpos)
  refine ⟨max A 0*max B 0,?_⟩
  intro g p hp hq
  let q := cubicThetaMobius (cubicThetaFullComplex g) p
  let r := cubicThetaPrimitiveRow g
  have hp0 := hKpos p hp
  have hq0 : 0<q.2 := hLpos q hq
  have he : r.denominator p=p.2/q.2 := by
    change r.denominator p=p.2/r.height p
    unfold CubicThetaPrimitiveRow.height
    field_simp [(r.denominator_pos hp0).ne',hp0.ne']
  have hrow := r.norm_sum_bound hp0
  have he' : (2+(1+2*Complex.normSq p.1)/p.2^2)*r.denominator p=
      heightControl p*(1/q.2) := by rw [he]; unfold heightControl; ring
  rw [he'] at hrow
  have hAp : heightControl p ≤ max A 0 :=
    (le_abs_self _).trans ((hA p hp).trans (le_max_left _ _))
  have hBq : 1/q.2 ≤ max B 0 :=
    (le_abs_self _).trans ((hB q hq).trans (le_max_left _ _))
  exact hrow.trans (mul_le_mul hAp hBq (by positivity) (le_max_right _ _))

end CubicFirstMoment

end

end OAI
