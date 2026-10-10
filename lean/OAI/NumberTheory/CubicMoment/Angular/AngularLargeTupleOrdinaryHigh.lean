import OAI.NumberTheory.CubicMoment.Angular.AngularLargeTupleGroupKernel
import OAI.NumberTheory.CubicMoment.Estimates.LargeTuplePieceWitness
import OAI.NumberTheory.CubicMoment.Estimates.FiniteBilinearConstants

namespace OAI

/-! Actual high boxes having an ordinary surviving tuple. A single fixed
group works for the entire box, and constants are uniform over the finite
set of possible groups. The original sharp cutoff is retained. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_largePrimeTuplePiece_ordinary_high_log_saving (i j : ℕ)
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : 0 < δ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      (∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j ℓ ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          ¬largePrimeTupleExceptional δ q) →
      ‖largePrimeTuplePiece i j ℓ ξ Ct H X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  let S := {s : Finset (Fin i ⊕ Fin j) // s.Nonempty}
  have hdata (s : S) := angular_large_tuple_group_low_kernel ℓ s.1 s.2 hSW hℓ hpub hHuxley hperiod
    hMV hC hξ hξz hGI hGQ hVor hGamma k Ct
  choose η G K B hη hη1 hK hbound using hdata
  obtain ⟨η₀,G₀,K₀,B₀,hη₀,_hη₀1,hK₀,hdom⟩ := finite_bilinear_constants η K B G hη
  obtain ⟨ε,hε,hrange⟩ := largePrimeTuplePiece_ordinary_range i j hξ hξz hδ
  have hall := (Filter.eventually_all).mpr hbound
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  refine ⟨(‖c‖+1)*K₀,by positivity,?_⟩
  filter_upwards [hall,hrange hη₀ G₀,largePrimeTuplePiece_rough_scales i j hξ hξz,
    eventually_largePrimeTuplePiece_high_full i j hξz,eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)).eventually_ge_atTop B₀]
    with X hbound hrange hrough hfull hX hB₀
  intro H hH d hhigh hex
  have hXp : 0 < X := zero_lt_one.trans hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  by_cases hz : largePrimeTuplePiece i j ℓ ξ Ct H X d = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨q,hq,hne,hordinary⟩ := hex
  obtain ⟨hcoord,hrough⟩ := hrough ℓ Ct H d q hq hne
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hcoord⟩
  obtain ⟨s,hBX,hsq,hprodlo,hprodhi,hAlo,hAhi⟩ := hrange ℓ Ct H d q hq hne hordinary
  have hss : s.Nonempty := by
    by_contra hn
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [hs0,largeTupleSubsetScale,Finset.prod_empty] at hBX
    exact (not_le_of_gt (Real.one_lt_rpow hX (by linarith : (0:ℝ) < 1/3+ε))) hBX
  let ss : S := ⟨s,hss⟩
  obtain ⟨hηs,hGs,hKs,hBs⟩ := hdom ss
  let A := largeTupleGroupLength (Finset.univ\s) z
  let L := largeTupleGroupLength s z
  have hLp : 0 < L := zero_lt_one.trans_le (largeTupleGroupLength_one s z)
  have hL1 : 1 ≤ L := largeTupleGroupLength_one s z
  have hLX : X^(1/3:ℝ) ≤ L :=
    (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith : (1/3:ℝ) ≤ 1/3+ε)).trans hBX
  have hLB : L ≤ 3*X := by change L^2 ≤ 3*X at hsq; nlinarith
  have hAL : L^(1-η ss/16) ≤ A :=
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)).trans hAlo
  have hAH : A ≤ L^2/(1+Real.log L)^(G ss) := by
    have hlogL : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL1]
    exact hAhi.trans (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hlogL _)
      (pow_le_pow_right₀ (by linarith [Real.log_nonneg hL1]) hGs))
  have hh := hbound ss z H rfl hH hLX hprodhi (hBs.trans (hB₀.trans hLX))
    (fun a => hrough L hLp.le hLB a) hAL hAH
  have he := hfull ℓ Ct H d hhigh hz
  rw [he,largeTupleIndependentSum_regroup i j ℓ ξ Ct H X (fun a => (d a).val) s,norm_mul]
  change ‖c‖*‖largeTupleRegroupedKernel i j ℓ ξ Ct H X z.1.2 s‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hh (_root_.norm_nonneg c)).trans
  have hcK : ‖c‖*K ss ≤ (‖c‖+1)*K₀ := by
    have hc := mul_le_mul_of_nonneg_left hKs (_root_.norm_nonneg c)
    nlinarith
  calc
    _ = (‖c‖*K ss)*(X^(5/6:ℝ)/(1+Real.log X)^k) := by ring
    _ ≤ ((‖c‖+1)*K₀)*(X^(5/6:ℝ)/(1+Real.log X)^k) :=
      mul_le_mul_of_nonneg_right hcK (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
