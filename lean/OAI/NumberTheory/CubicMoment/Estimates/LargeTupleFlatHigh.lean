import OAI.NumberTheory.CubicMoment.Estimates.FlatTripleGeometry
import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleTripleKernel

namespace OAI

/-! Flat high boxes in the actual norm partition. The largest prime
coordinate yields the transition range; the original cutoff is retained. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem largePrimeTuplePiece_flat_high_bound (i j : ℕ) (hij : i+j = 3)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C ξ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (Ct G : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ∀ d ∈ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X,
      X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      ‖largePrimeTuplePiece i j 0 ξ Ct H X d‖ ≤
        K*X^(5/6:ℝ)*(1+Real.log (1+Real.log X))/(1+Real.log X)^(3/2:ℝ) := by
  have hdata (a : Fin i ⊕ Fin j) := large_tuple_triple_low_kernel (ξ := ξ) hij a hpnt hSW hpub
    hHuxley hperiod hMV hC (show 0 < ξ/2 by positivity) hGI hGQ Ct
  choose η K B₀ hη hη1 hK hbound using hdata
  let K₀ : ℝ := 1+∑ a, K a
  have hK₀ : 0 < K₀ := by
    have hh := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin i ⊕ Fin j)))
      (fun a _ => (hK a).le)
    dsimp [K₀]
    linarith
  have hKle (a : Fin i ⊕ Fin j) : K a ≤ K₀ := by
    have hh := Finset.single_le_sum (fun b _ => (hK b).le) (Finset.mem_univ a)
    dsimp [K₀]
    linarith
  have hB₀ := (Filter.eventually_all).mpr (fun a =>
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop (B₀ a))
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  refine ⟨(‖c‖+1)*K₀,by positivity,?_⟩
  filter_upwards [(Filter.eventually_all).mpr hbound,hB₀,
    eventually_flatTriple_transition_geometry hij G,largePrimeTuplePiece_rough_scales i j hξ hξz,
    eventually_largePrimeTuplePiece_high_full i j hξz,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_gt_atTop 2,
    eventually_ge_atTop (1:ℝ)] with X hb hB₀ hgeometry hrough hfull hlarge hX
  intro H hH d hd hhigh
  obtain ⟨_,hne,B,hB,hflat⟩ := Finset.mem_filter.mp hd
  obtain ⟨q,hq,hqne⟩ := largePrimeTuplePiece_witness d hne
  obtain ⟨hcoord,hrough⟩ := hrough 0 Ct H d q hq hqne
  let z : largeTupleBoxIndex i j := ⟨(⟨X,zero_lt_one.trans_le hX⟩,fun a => (d a).val),hcoord⟩
  let : Nonempty (Fin i ⊕ Fin j) := Fintype.card_pos_iff.mp (by simp [hij])
  obtain ⟨a,_ha,hmax⟩ := Finset.exists_max_image Finset.univ
    (largeTupleNormScale z.1.2) Finset.univ_nonempty
  have hmax' : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a :=
    fun b => hmax b (Finset.mem_univ b)
  have hrange := largePrimeTuplePiece_scale_product (zero_lt_one.trans_le hX) d hqne
  change X/(2*2^(i+j)) ≤ (∏ b, largeTupleNormScale z.1.2 b) ∧
    (∏ b, largeTupleNormScale z.1.2 b) ≤ 3*X at hrange
  rw [hij] at hrange
  norm_num only [pow_succ,pow_zero,mul_one] at hrange
  have hflat' : (largeTupleNormScale z.1.2 a)^3 ≤
      (∏ b, largeTupleNormScale z.1.2 b)*(1+Real.log X)^G :=
    (pow_le_pow_left₀ (largeTupleNormScale_pos _ _).le (hB a) 3).trans hflat
  obtain ⟨hBX,hBA,hAB⟩ := hgeometry z a hmax' (by simpa using hrange.1) hflat'
  have hp : largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a ≤ 3*X := by
    rw [largeTuple_singleton_product]
    exact hrange.2
  have hBpos : 0 < largeTupleNormScale z.1.2 a := largeTupleNormScale_pos _ _
  have hBlarge : 2 < largeTupleNormScale z.1.2 a := hlarge.trans_le hBX
  have hBupper : largeTupleNormScale z.1.2 a ≤ 3*X := by
    have hAone := largeTupleGroupLength_one (Finset.univ\{a}) z
    nlinarith
  have hsqrt : (2*largeTupleNormScale z.1.2 a)^(1/2:ℝ) < largeTupleNormScale z.1.2 a := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_lt' hBpos).mpr
    nlinarith
  have hk := hb a z H rfl hH hBX hp ((hB₀ a).trans hBX) hsqrt
    ((Real.rpow_le_self_of_one_le (z.property a) (by linarith [hη a])).trans hBA) hAB (by
      intro b
      apply (Real.rpow_le_rpow hBpos.le (by linarith : largeTupleNormScale z.1.2 a ≤
        2*largeTupleNormScale z.1.2 a) (by positivity : (0:ℝ) ≤ ξ/2)).trans
      exact (hrough _ hBpos.le hBupper b).le)
  rw [hfull 0 Ct H d hhigh hne,largeTupleIndependentSum_regroup i j 0 ξ Ct H X z.1.2 {a},norm_mul]
  change ‖c‖*‖largeTupleRegroupedKernel i j 0 ξ Ct H X z.1.2 {a}‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hk (_root_.norm_nonneg c)).trans
  have hconst : ‖c‖*K a ≤ (‖c‖+1)*K₀ := by
    nlinarith [mul_le_mul_of_nonneg_left (hKle a) (_root_.norm_nonneg c)]
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hlog : 0 ≤ 1+Real.log (1+Real.log X) := by
    have hh := Real.log_nonneg (show 1 ≤ 1+Real.log X by linarith [Real.log_nonneg hX])
    linarith
  calc
    _ = (‖c‖*K a)*(X^(5/6:ℝ)*(1+Real.log (1+Real.log X))/(1+Real.log X)^(3/2:ℝ)) := by ring
    _ ≤ ((‖c‖+1)*K₀)*(X^(5/6:ℝ)*(1+Real.log (1+Real.log X))/(1+Real.log X)^(3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
