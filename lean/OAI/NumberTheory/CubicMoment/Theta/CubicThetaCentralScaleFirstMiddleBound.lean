import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstMiddleBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralLargeTupleGroupKernel

namespace OAI

/-! The actual scale-first boxes between X^.345 and X^.38 have arbitrary
logarithmic saving, using the distinguished coordinates as a fixed group. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem scaleFirstPrimeTuplePiece_middle_bound_actual (i j : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(69/200:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      largeTupleDistinguishedScale (fun a => (d a).val) < X^(38/100:ℝ) →
      ‖scaleFirstPrimeTuplePiece i j 0 ξ Ct H X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  let s := distinguishedCoordinateSet i j
  by_cases hs : s.Nonempty
  · obtain ⟨η,G,K,B₀,hη,_hη1,hK,hbound⟩ := large_tuple_group_low_kernel_actual s hs
      hSW hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma k Ct
    let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
    refine ⟨(‖c‖+1)*K,by positivity,?_⟩
    filter_upwards [hbound,eventually_scaleFirst_middle_range i j hη G,
      scaleFirstPrimeTuplePiece_rough_scales i j hξ hξz,
      scaleFirstPrimeTuplePiece_coordinate_envelope i j hξz,
      eventually_gt_atTop (1:ℝ),
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).eventually_ge_atTop B₀]
      with X hbound hrange hrough henv hX hB₀
    intro H hH d hhigh hlow
    have hL : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
    by_cases hz : scaleFirstPrimeTuplePiece i j 0 ξ Ct H X d = 0
    · rw [hz,norm_zero]
      positivity
    have hw : ∃ q ∈ largePrimeTupleBox i j X,
        uncutPrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hz
      unfold scaleFirstPrimeTuplePiece
      rw [Finset.sum_eq_zero hn,mul_zero]
    obtain ⟨q,hq,hne⟩ := hw
    obtain ⟨hcoord,hrough⟩ := hrough 0 Ct H d q hq hne
    let z : largeTupleBoxIndex i j := ⟨(⟨X,zero_lt_one.trans hX⟩,fun a => (d a).val),hcoord⟩
    obtain ⟨hBX,hprod,hAlo,hAhi⟩ := hrange 0 ξ Ct H d hhigh hlow q hne
    let B := largeTupleGroupLength s z
    have hBp : 0 < B := zero_lt_one.trans_le (largeTupleGroupLength_one s z)
    have hBhi : B ≤ 3*X := by
      have hone := largeTupleGroupLength_one (Finset.univ\s) z
      exact (le_mul_of_one_le_left hBp.le hone).trans hprod
    have hh := hbound z H rfl hH hBX hprod (hB₀.trans hBX)
      (fun a => hrough B hBp.le hBhi a) hAlo hAhi
    rw [scaleFirstPrimeTuplePiece_full i j 0 ξ Ct H X d (henv 0 Ct H d hhigh q hq hne),
      largeTupleIndependentSum_regroup i j 0 ξ Ct H X (fun a => (d a).val) s,norm_mul]
    change ‖c‖*‖largeTupleRegroupedKernel i j 0 ξ Ct H X z.1.2 s‖ ≤ _
    apply (mul_le_mul_of_nonneg_left hh (_root_.norm_nonneg c)).trans
    have hk : ‖c‖*K ≤ (‖c‖+1)*K := by nlinarith [hK]
    calc
      _ = (‖c‖*K)*(X^(5/6:ℝ)/(1+Real.log X)^k) := by ring
      _ ≤ ((‖c‖+1)*K)*(X^(5/6:ℝ)/(1+Real.log X)^k) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = _ := by ring
  · refine ⟨1,by norm_num,?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    intro H hH d hhigh _
    exact (hs (distinguishedCoordinateSet_nonempty hX (fun a => (d a).val) hhigh)).elim

end CubicFirstMoment

end

end OAI
