import OAI.NumberTheory.CubicMoment.Angular.AngularTailPrimeTailGeometry
import OAI.NumberTheory.CubicMoment.Angular.AngularTailPrimeUpperGroupBound
import OAI.NumberTheory.CubicMoment.Estimates.UpperHeightSuffix

namespace OAI

/-! Each upper-height tuple is one aligned suffix. A surviving term chooses
one group for the whole suffix, before applying any norm estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

def angular_tailPrimeUpperTuple (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  ∑ v ∈ Finset.range (heightWindowCount H T),
    if X^(1/100:ℝ) < T*(3/2:ℝ)^v then
      tailPrimeTuplePiece i j ℓ ξ H (T*(3/2:ℝ)^v) X d else 0

lemma angular_tailPrimeUpperTuple_suffix (i j : ℕ) (ξ H T X : ℝ)
    (d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
    (hH : 0 < H) (hT : 0 < T) :
    ∃ v ≤ heightWindowCount H T,
      (v < heightWindowCount H T → X^(1/100:ℝ) < T*(3/2:ℝ)^v) ∧
      angular_tailPrimeUpperTuple ℓ i j ξ H T X d =
        angular_tailPrimeTupleTail ℓ i j ξ H (T*(3/2:ℝ)^v) X d := by
  exact geometricHeight_filtered_suffix
    (fun U => tailPrimeTuplePiece i j ℓ ξ H U X d) hH hT _

theorem angular_tailPrime_upper_tuple_bound_uniform
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/36 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 2/5 →
      ∀ i j n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H T : ℝ, Real.log X ≤ T → 1 ≤ H → H ≤ X^(1/6+1/3000:ℝ) →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(1/3-2*κ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      ‖angular_tailPrimeUpperTuple ℓ i j ξ H T X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hgroup⟩ :=
    angular_tailPrime_upper_group_bound_uniform ℓ hpub hHuxley hperiod hMV hC hGI hGQ
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle ξ hξ hξz i j n
  have hκsmall : κ < 1/12 := by linarith
  have hdata (s : Finset (Fin i ⊕ Fin j)) := hgroup κ hκ hκle ξ hξ hξz i j s n
  choose K hK hb using hdata
  have hall := (Filter.eventually_all).mpr hb
  let M : ℝ := 1+∑ s, |K s|
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨(‖c‖+1)*M,by positivity,?_⟩
  filter_upwards [hall,angular_eventually_tailPrimeTupleTail_groups ℓ i j hκ hκsmall hξ hξz,
    eventually_gt_atTop (1:ℝ)] with X hbound hgeom hX
  intro H T hT hH hHX d hd
  have hXp : 0 < X := zero_lt_one.trans hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  have hTp : 0 < T := (Real.log_pos hX).trans_le hT
  obtain ⟨v,_hv,hstart,he⟩ := angular_tailPrimeUpperTuple_suffix ℓ i j ξ H T X d
    (zero_lt_one.trans_le hH) hTp
  rw [he]
  by_cases hz : angular_tailPrimeTupleTail ℓ i j ξ H (T*(3/2:ℝ)^v) X d = 0
  · rw [hz,norm_zero]
    positivity
  have hv : v < heightWindowCount H T := by
    by_contra hn
    have hc : heightWindowCount H (T*(3/2:ℝ)^v) = 0 := by
      rw [heightWindowCount_shift (zero_lt_one.trans_le hH) hTp]
      omega
    apply hz
    simp only [angular_tailPrimeTupleTail,hc,Finset.range_zero,Finset.sum_empty]
  obtain ⟨s,hBlo,hBsq,hABlo,hABhi,hcoord,hrough,hid⟩ :=
    hgeom H (T*(3/2:ℝ)^v) d hd hz
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hcoord⟩
  have hb := hbound s z H (T*(3/2:ℝ)^v) rfl hBlo hBsq hABlo hABhi
    (fun a => hrough a) (hstart hv).le hH hHX
  rw [hid H (T*(3/2:ℝ)^v),norm_mul]
  change ‖c‖ * ‖envelopeCutoffBilinearTail _ _ _ _ _ H _ X‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hb (_root_.norm_nonneg c)).trans
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
