import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeUpperTuple
import OAI.NumberTheory.CubicMoment.Estimates.TailHighDecomposition
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleCount

namespace OAI

/-! The complete upper high-scale prime contribution, including all norm
partitions and the finite arity expansion. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeUpperTupleSum (i j : ℕ) (κ ξ H T X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      tailPrimeUpperTuple i j ξ H T X d else 0

theorem tailHighUpperArity_collection {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (κ H T : ℝ),
      tailHighUpperArity i κ ξ H T X =
        ∑ j ∈ Finset.range m, tailPrimeUpperTupleSum i j κ ξ H T X := by
  obtain ⟨m,hm⟩ := tailHighScaleRows_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hr
  intro i κ H T
  unfold tailHighUpperArity
  simp_rw [hr i 0 H]
  calc
    _ = ∑ v ∈ Finset.range (heightWindowCount H T), ∑ j ∈ Finset.range m,
        ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          if X^(1/100:ℝ) < T*(3/2:ℝ)^v then
            if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
              tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp only [Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      unfold tailPrimeUpperTupleSum
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
      · simp only [hd,ite_true,tailPrimeUpperTuple]
      · simp only [hd,ite_false,ite_self,Finset.sum_const_zero]

theorem tailHighUpperArity_isLittleO_uniform
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ (i : ℕ) (H T : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => tailHighUpperArity i κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hbound⟩ :=
    tailPrime_upper_tuple_bound_uniform hpub hHuxley hperiod hMV hC hGI hGQ
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle ξ hξ hξz i H T hT hH hHX
  obtain ⟨m,hm⟩ := tailHighUpperArity_collection hξ
  have hpart (j : ℕ) :
      (fun X => tailPrimeUpperTupleSum i j κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
    obtain ⟨K,hK,hb⟩ := hbound κ hκ hκle ξ hξ hξz i j (3+(i+j))
    obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K)
    filter_upwards [hb,hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X hb ht hh hx hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    have hB : 0 ≤ K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
          tailPrimeUpperTuple i j ξ (H X) (T X) X d else 0‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by
      split_ifs with hd
      · exact hb (H X) (T X) ht hh hx d hd
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold tailPrimeUpperTupleSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    rw [pow_add]
    field_simp [hL.ne']
    ring
  have hs := Asymptotics.IsLittleO.fun_sum (s := Finset.range m) (fun j _ => hpart j)
  apply hs.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hx
  exact (hx i κ (H X) (T X)).symm

end CubicFirstMoment

end

end OAI
