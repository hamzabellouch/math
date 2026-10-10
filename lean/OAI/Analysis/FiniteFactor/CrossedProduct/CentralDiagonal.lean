import OAI.Analysis.FiniteFactor.CrossedProduct.WeightedShiftField
import OAI.Analysis.FiniteFactor.CrossedProduct.FreeRotation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceFirstMultiplier : SourceBaseFunction where
  toFun x := (x sourceFirstCoordinate : ℂ)
  measurable := Complex.measurable_ofReal.comp (measurable_pi_apply sourceFirstCoordinate)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le x hx := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx sourceFirstCoordinate).1]
    exact (hx sourceFirstCoordinate).2.le

theorem sourceFirstMultiplier_distinct (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (x : SourceCoordinate → ℝ)
    (n k : ℤ) (hnk : n ≠ k) :
    sourceFirstMultiplier.toFun (coordinateRotate θ n x) ≠
      sourceFirstMultiplier.toFun (coordinateRotate θ k x) := by
  intro he
  have he' := Complex.ofReal_injective he
  change Int.fract (x sourceFirstCoordinate+(n : ℝ)*θ sourceFirstCoordinate) =
    Int.fract (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate) at he'
  rw [Int.fract,Int.fract] at he'
  apply hr.mul_ne_integer sourceFirstCoordinate (n-k) (sub_ne_zero.mpr hnk)
    (Int.floor (x sourceFirstCoordinate+(n : ℝ)*θ sourceFirstCoordinate) -
      Int.floor (x sourceFirstCoordinate+(k : ℝ)*θ sourceFirstCoordinate))
  push_cast
  nlinarith

/-- The field of pi(g) has its actual diagonal action on every vector. -/
theorem sourceOperatorField_pi_action (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (v : SourceFiberHilbert) (k : ℤ),
      sourceOperatorField (sourcePi θ g) x v k = g.toFun (coordinateRotate θ k x) * v k := by
  have hm := ae_all_iff.mpr (sourceMatrixEntry_pi θ g)
  filter_upwards [hm,sourceOperatorField_entries_ae θ (sourcePi_mem θ g)] with x hm he v k
  rw [fiberOperator_action]
  simp_rw [he,hm]
  have hs : (fun n : ℤ => (if k = n then g.toFun (coordinateRotate θ n x) else 0) * v n) =
      fun n => if n = k then g.toFun (coordinateRotate θ k x) * v k else 0 := by
    funext n
    by_cases hn : n = k
    · subst n; simp
    · simp [hn,Ne.symm hn]
  rw [hs]
  simp

/-- Commutation in the source algebra passes to the actual fields. -/
theorem sourceOperatorField_commute (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) (hAB : A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField A x * sourceOperatorField B x =
      sourceOperatorField B x * sourceOperatorField A x := by
  filter_upwards [sourceOperatorField_mul θ hA hB,sourceOperatorField_mul θ hB hA] with x h₁ h₂
  rw [← h₁,← h₂,hAB]

/-- Distinct diagonal eigenvalues force every off-diagonal matrix coefficient
of a commuting bounded operator to vanish. -/
theorem fiber_commuting_diagonal_entry
    (A G : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (d : ℤ → ℂ)
    (hG : ∀ v k, G v k = d k * v k) (hAG : A*G = G*A)
    (n k : ℤ) (hd : d n ≠ d k) : A (lp.single 2 n (1 : ℂ)) k = 0 := by
  have hsingle : G (lp.single 2 n (1 : ℂ)) = d n • lp.single 2 n (1 : ℂ) := by
    classical
    apply Subtype.ext
    funext j
    change G (lp.single 2 n (1 : ℂ)) j = d n * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) j
    rw [hG]
    by_cases hj : n = j
    · subst j; rfl
    · simp [lp.single_apply,hj]
  have he := congrArg (fun T : SourceFiberHilbert →L[ℂ] SourceFiberHilbert =>
    T (lp.single 2 n (1 : ℂ)) k) hAG
  change A (G (lp.single 2 n (1 : ℂ))) k = G (A (lp.single 2 n (1 : ℂ))) k at he
  rw [hsingle,map_smul,hG] at he
  change d n * A (lp.single 2 n (1 : ℂ)) k = d k * A (lp.single 2 n (1 : ℂ)) k at he
  exact (mul_eq_mul_right_iff.mp he).resolve_left hd

theorem sourceCentral_offDiagonal_zero (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ)
    (hcentral : ∀ B ∈ sourceAlgebra θ, A*B = B*A) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n k : ℤ, n ≠ k →
      sourceOperatorField A x (lp.single 2 n (1 : ℂ)) k = 0 := by
  filter_upwards [sourceOperatorField_pi_action θ sourceFirstMultiplier,
    sourceOperatorField_commute θ hA (sourcePi_mem θ sourceFirstMultiplier)
      (hcentral _ (sourcePi_mem θ sourceFirstMultiplier))] with x hG hc n k hnk
  exact fiber_commuting_diagonal_entry _ _ _ hG hc n k (sourceFirstMultiplier_distinct θ hr x n k hnk)

end
end FiniteFactor

end OAI
