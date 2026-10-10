import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleNonflatHigh
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralLargeTupleNearFlatKernel

namespace OAI

/-! The high exceptional triples outside the counted flat set have a
logarithmic bilinear gap. Their actual smooth boxes therefore have
arbitrary logarithmic saving. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem largePrimeTuplePiece_nonflat_high_bound_actual (i j : ℕ) (hij : i+j = 3)
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C ξ δ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hδ : δ ≤ 1/12)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ H : ℝ, 0 < H →
      ∀ d : (Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      X^(38/100:ℝ) ≤ largeTupleDistinguishedScale (fun a => (d a).val) →
      d ∉ largePrimeTupleFlatBoxSet i j 0 ξ Ct G H X →
      (∃ q ∈ largePrimeTupleBox i j X,
        largePrimeTupleTerm i j 0 ξ Ct H X q*normTupleWeight d (largePrimeTupleNorm q) ≠ 0 ∧
          largePrimeTupleExceptional δ q) →
      ‖largePrimeTuplePiece i j 0 ξ Ct H X d‖ ≤ K*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hdata (a : Fin i ⊕ Fin j) := large_tuple_quarter_group_low_kernel_actual {a} (by simp)
    hSW hpub hHuxley hperiod hMV hC hξ hξz hGI hGQ  hGamma k Ct
  choose η G K B₀ hη hη1 hK hbound using hdata
  let G₀ : ℕ := 1+∑ a, G a
  have hGle (a : Fin i ⊕ Fin j) : G a+1 ≤ G₀ := by
    have hh := Finset.single_le_sum (fun b _ => Nat.zero_le (G b)) (Finset.mem_univ a)
    dsimp [G₀]
    omega
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
  have hloglimit : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hloglarge := (Filter.eventually_all).mpr (fun a =>
    hloglimit.eventually_ge_atTop
      (max 2 ((2:ℝ)^(G a))))
  let c : ℂ := (i.factorial:ℂ)⁻¹*(j.factorial:ℂ)⁻¹
  refine ⟨G₀,(‖c‖+1)*K₀,by positivity,?_⟩
  filter_upwards [(Filter.eventually_all).mpr hbound,hB₀,hloglarge,
    exceptionalTriple_scale_square i j hδ,eventually_maximum_triple_scale,
    largePrimeTuplePiece_rough_scales i j hξ hξz,
    eventually_largePrimeTuplePiece_high_full i j hξz,eventually_ge_atTop (1:ℝ)]
    with X hb hB₀ hloglarge hsquare hquarter hrough hfull hX
  intro H hH d hhigh hnot hex
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  by_cases hne : largePrimeTuplePiece i j 0 ξ Ct H X d = 0
  · rw [hne,norm_zero]
    positivity
  obtain ⟨q,hq,hqne,hqex⟩ := hex
  obtain ⟨hcoord,hrough⟩ := hrough 0 Ct H d q hq hqne
  let z : largeTupleBoxIndex i j := ⟨(⟨X,hXp⟩,fun a => (d a).val),hcoord⟩
  let : Nonempty (Fin i ⊕ Fin j) := Fintype.card_pos_iff.mp (by simp [hij])
  obtain ⟨a,_ha,hmax⟩ := Finset.exists_max_image Finset.univ
    (largeTupleNormScale z.1.2) Finset.univ_nonempty
  have hmax' : ∀ b, largeTupleNormScale z.1.2 b ≤ largeTupleNormScale z.1.2 a :=
    fun b => hmax b (Finset.mem_univ b)
  have hrange := largePrimeTuplePiece_scale_product hXp d hqne
  change X/(2*2^(i+j)) ≤ (∏ b, largeTupleNormScale z.1.2 b) ∧
    (∏ b, largeTupleNormScale z.1.2 b) ≤ 3*X at hrange
  rw [hij] at hrange
  norm_num only [pow_succ,pow_zero,mul_one] at hrange
  have hBpos := largeTupleNormScale_pos z.1.2 a
  have hBX := hquarter _ _ hBpos.le (by simpa using hrange.1)
    (largeTuple_product_le_cube hij z a hmax')
  have hp : largeTupleGroupLength (Finset.univ\{a}) z*largeTupleNormScale z.1.2 a ≤ 3*X := by
    rw [largeTuple_singleton_product]
    exact hrange.2
  have hBupper : largeTupleNormScale z.1.2 a ≤ 3*X := by
    have hAone := largeTupleGroupLength_one (Finset.univ\{a}) z
    nlinarith
  have hBA : largeTupleNormScale z.1.2 a ≤ largeTupleGroupLength (Finset.univ\{a}) z := by
    have hh := hsquare 0 ξ Ct H d q hq hqne hqex a
    change (largeTupleNormScale z.1.2 a)^2 ≤ (∏ b, largeTupleNormScale z.1.2 b) at hh
    rw [← largeTuple_singleton_product z a,pow_two] at hh
    exact (mul_le_mul_iff_right₀ hBpos).mp (by simpa only [mul_comm] using hh)
  have hgap := nonflat_singleton_length_gap z a hLX G₀ hmax' (by
    intro h
    apply hnot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,h⟩)
  have hden := nearFlat_log_denominator hX (z.property a) hBupper (hGle a) (hloglarge a)
  have hLB : 0 < 1+Real.log (largeTupleNormScale z.1.2 a) := by
    linarith [Real.log_nonneg (z.property a)]
  have hAhi := hgap.trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden)
  have hAlow : (largeTupleNormScale z.1.2 a)^(1-η a/16) ≤
      largeTupleGroupLength (Finset.univ\{a}) z := (Real.rpow_le_self_of_one_le (z.property a) (by linarith [hη a])).trans hBA
  have hk := hb a z H rfl hH
  simp only [largeTupleGroupLength,Finset.prod_singleton] at hk
  have hh := hk hBX hp ((hB₀ a).trans hBX)
    (fun b => hrough _ hBpos.le hBupper b) hAlow hAhi
  rw [hfull 0 Ct H d hhigh hne,largeTupleIndependentSum_regroup i j 0 ξ Ct H X z.1.2 {a},norm_mul]
  change ‖c‖*‖largeTupleRegroupedKernel i j 0 ξ Ct H X z.1.2 {a}‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hh (_root_.norm_nonneg c)).trans
  have hconst : ‖c‖*K a ≤ (‖c‖+1)*K₀ := by
    nlinarith [mul_le_mul_of_nonneg_left (hKle a) (_root_.norm_nonneg c)]
  calc
    _ = (‖c‖*K a)*(X^(5/6:ℝ)/(1+Real.log X)^k) := by ring
    _ ≤ ((‖c‖+1)*K₀)*(X^(5/6:ℝ)/(1+Real.log X)^k) :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
