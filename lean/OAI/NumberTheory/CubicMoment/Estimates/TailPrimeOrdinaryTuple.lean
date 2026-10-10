import OAI.NumberTheory.CubicMoment.Estimates.TailPrimeOrdinaryBounds

namespace OAI

/-! A surviving ordinary prefix fixes independent prime groups. Constants
and logarithmic thresholds are uniform over the finite choices of group. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def tailPrimeOrdinaryTuple (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
      tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d else 0

lemma tailPrimeTupleRegrouped_window (i j : ℕ) (ℓ : ℤ) (ξ H U X : ℝ)
    (d : (Fin i ⊕ Fin j) → ℕ) (s : Finset (Fin i ⊕ Fin j)) :
    tailPrimeTupleRegrouped i j ℓ ξ H U X d s =
      productGaussWindow (largeTupleSelectedSupport ξ X d s)
        (largeTupleOtherSupport ξ X d s) (largeTupleSelectedCoefficient ξ X d s)
        (largeTupleOtherCoefficient ξ X d s) ℓ primeProductEnvelope H U X := rfl

theorem tailPrime_ordinary_tuple_bound (i j : ℕ)
    (hpnt : PrimaryPrimePNT) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (n : ℕ) :
    ∃ (Ct : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H T : ℝ, (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      ‖tailPrimeOrdinaryTuple i j ξ H T X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  have hdata (s : Finset (Fin i ⊕ Fin j)) := tailPrime_ordinary_group_prefix s hpnt hpub
    hHuxley hperiod hMV hC hξ hξz hGI hGQ n
  choose Ct K hK hb using hdata
  have hall := (Filter.eventually_all).mpr hb
  let Ct₀ := Finset.univ.sup Ct
  let M : ℝ := 1+∑ s, |K s|
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨Ct₀,(‖c‖+1)*M,by positivity,?_⟩
  filter_upwards [hall,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1000,
    eventually_tailPrimeTuple_coordinate_envelope (i := i) (j := j)
      (κ := 0) (by norm_num) (by norm_num) hξz,
    tailPrimeTuplePiece_rough_scales i j hξ hξz] with X hbound hX hlog hcoord hrough
  intro H T hT hH hHX d hhigh
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 < 1+Real.log X := by linarith
  by_cases hz : tailPrimeOrdinaryTuple i j ξ H T X d = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨v,_hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hpne : tailPrimeTuplePiece i j 0 ξ H (T*(3/2:ℝ)^v) X d ≠ 0 := by
    intro hn
    apply hvn
    simp only [hn,ite_self]
  obtain ⟨q,hq,hqn⟩ := tailPrimeTuplePiece_witness d hpne
  obtain ⟨s,hBlo,hBsq⟩ := tailPrimeTupleOrdinary_group hX hlog hξ hξz d hhigh hq hqn
  have hp := tailPrimeTuple_scale_product hXp d hqn
  have hr := hrough 0 H (T*(3/2:ℝ)^v) d q hq hqn
  have hprod : largeTupleSubsetScale (fun a => (d a).val) (Finset.univ\s)*
      largeTupleSubsetScale (fun a => (d a).val) s =
      largeTupleSubsetScale (fun a => (d a).val) Finset.univ := by
    rw [mul_comm,largeTupleSubsetScale_complement]
  have hB3 : largeTupleSubsetScale (fun a => (d a).val) s ≤ 3*X := by
    have hpos := largeTupleSubsetScale_pos (fun a => (d a).val) s
    nlinarith
  have hhigh' : X^(1/3-2*(0:ℝ)) ≤ largeTupleDistinguishedScale (fun a => (d a).val) :=
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1/3-2*(0:ℝ)) ≤ 69/200)).trans hhigh
  have hcoords := hcoord 0 H (T*(3/2:ℝ)^v) d hhigh' q hq hqn
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hr.1⟩
  have hTs : (1+Real.log X)^(Ct s) ≤ T :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ 1+Real.log X)
      (Finset.le_sup (f := Ct) (Finset.mem_univ s))).trans hT
  have hprefix := hbound s z H T rfl hBlo hBsq
    (by change X/(2*2^(i+j)) ≤ largeTupleSubsetScale (fun a => (d a).val) (Finset.univ\s)*largeTupleSubsetScale (fun a => (d a).val) s
        rw [hprod]; exact hp.1)
    (by change largeTupleSubsetScale (fun a => (d a).val) (Finset.univ\s)*largeTupleSubsetScale (fun a => (d a).val) s ≤ 3*X
        rw [hprod]; exact hp.2)
    (fun a => hr.2 _ (largeTupleSubsetScale_pos _ _).le hB3 a) hTs hH hHX
  have he : tailPrimeOrdinaryTuple i j ξ H T X d =
      c*(∑ v ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^v ≤ X^(1/100:ℝ) then
          productGaussWindow (largeTupleSelectedSupport ξ X (fun a => (d a).val) s)
            (largeTupleOtherSupport ξ X (fun a => (d a).val) s)
            (largeTupleSelectedCoefficient ξ X (fun a => (d a).val) s)
            (largeTupleOtherCoefficient ξ X (fun a => (d a).val) s)
            0 primeProductEnvelope H (T*(3/2:ℝ)^v) X else 0) := by
    unfold tailPrimeOrdinaryTuple
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : T*(3/2:ℝ)^w ≤ X^(1/100:ℝ)
    · simp only [hw,ite_true,tailPrimeTuplePiece_full i j 0 ξ H _ X d hcoords,
        tailPrimeTupleIndependent_regroup i j 0 ξ H _ X _ s,tailPrimeTupleRegrouped_window]
      rfl
    · simp only [hw,ite_false,mul_zero]
  rw [he,norm_mul]
  apply (mul_le_mul_of_nonneg_left hprefix (_root_.norm_nonneg c)).trans
  have hKM : K s ≤ M := by
    have hh := Finset.single_le_sum (fun t _ => abs_nonneg (K t)) (Finset.mem_univ s)
    dsimp [M]
    linarith [le_abs_self (K s)]
  have hconst : ‖c‖*K s ≤ (‖c‖+1)*M := by
    have hm := mul_le_mul_of_nonneg_left hKM (_root_.norm_nonneg c)
    nlinarith
  calc
    _ = (‖c‖*K s)*(X^(5/6:ℝ)/(1+Real.log X)^n) := by ring
    _ ≤ ((‖c‖+1)*M)*(X^(5/6:ℝ)/(1+Real.log X)^n) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
