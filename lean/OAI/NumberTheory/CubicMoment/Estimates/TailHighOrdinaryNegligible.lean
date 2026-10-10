import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeOrdinaryTuple
import OAI.NumberTheory.CubicMoment.Estimates.TailHighDecomposition
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleCount

namespace OAI

/-! The full ordinary high-scale contribution, including the finite arity
expansion and all smooth norm partitions. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeOrdinaryTupleSum (i j : ℕ) (ξ H T X : ℝ) : ℂ :=
  ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
      tailPrimeOrdinaryTuple i j ξ H T X d else 0

theorem tailHighOrdinaryArity_collection {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ m : ℕ, ∀ᶠ X : ℝ in atTop, ∀ (i : ℕ) (H T : ℝ),
      tailHighOrdinaryArity i ξ H T X =
        ∑ j ∈ Finset.range m, tailPrimeOrdinaryTupleSum i j ξ H T X := by
  obtain ⟨m,hm⟩ := tailHighScaleRows_arity hξ
  refine ⟨m,?_⟩
  filter_upwards [hm] with X hr
  intro i H T
  unfold tailHighOrdinaryArity
  simp_rw [hr i 0 H]
  calc
    _ = ∑ v ∈ Finset.range (heightWindowCount H T), ∑ j ∈ Finset.range m,
        ∑ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
          if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
            if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
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
      unfold tailPrimeOrdinaryTupleSum
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val)
      · simp only [hd,ite_true,tailPrimeOrdinaryTuple]
      · simp only [hd,ite_false,ite_self,Finset.sum_const_zero]

theorem tailHighOrdinaryArity_isLittleO (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ Ct : ℕ, ∀ H T : ℝ → ℝ,
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+1/3000:ℝ)) →
      (fun X => tailHighOrdinaryArity i ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨m,hm⟩ := tailHighOrdinaryArity_collection hξ
  have hdata (j : Fin m) := tailPrime_ordinary_tuple_bound i j hpnt hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ (3+(i+j))
  choose Ct K hK hb using hdata
  let Ct₀ := Finset.univ.sup Ct
  refine ⟨Ct₀,?_⟩
  intro H T hT hH hHX
  have hpart (j : Fin m) :
      (fun X => tailPrimeOrdinaryTupleSum i j ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
    obtain ⟨D,hD,hcount⟩ := largePrimeTuplePartition_count i j
    apply Asymptotics.IsBigO.trans_isLittleO
      (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
    apply Asymptotics.IsBigO.of_bound (D*K j)
    filter_upwards [hb j,hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X hb ht hh hx hX
    have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
    have ht' : (1+Real.log X)^(Ct j) ≤ T X :=
      (pow_le_pow_right₀ (by linarith [Real.log_nonneg hX])
        (Finset.le_sup (f := Ct) (Finset.mem_univ j))).trans ht
    have hKj : 0 < K j := hK j
    have hB : 0 ≤ K j*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by positivity
    have hp (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
        ‖if X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) then
          tailPrimeOrdinaryTuple i j ξ (H X) (T X) X d else 0‖ ≤
          K j*X^(5/6:ℝ)/(1+Real.log X)^(3+(i+j)) := by
      split_ifs with hd
      · exact hb (H X) (T X) ht' hh hx d hd
      · simpa only [norm_zero] using hB
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
    unfold tailPrimeOrdinaryTupleSum
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun d _ => hp d)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (hcount X hX) hB).trans_eq
    rw [pow_add]
    field_simp [hL.ne']
    ring
  have hs := Asymptotics.IsLittleO.fun_sum (s := Finset.univ) (fun j _ => hpart j)
  apply hs.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hm] with X hx
  rw [Fin.sum_univ_eq_sum_range (fun j => tailPrimeOrdinaryTupleSum i j ξ (H X) (T X) X)]
  exact (hx i (H X) (T X)).symm

end CubicFirstMoment

end

end OAI
