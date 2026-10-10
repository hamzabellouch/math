import OAI.NumberTheory.CubicMoment.Angular.AngularUniformHighStoppedTail
import OAI.NumberTheory.CubicMoment.Angular.AngularUpperLowTail

namespace OAI

/-! The upper low-scale estimate permits any sufficiently small positive
stopping exponent, compatible with the prime high-row estimate. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_upperStoppedTail_bound_uniform (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/12 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ i n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
        ∀ (H T : ℝ)
          (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
          (q : ℕ × ℕ × ℕ) (j k : ℕ),
        X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/2:ℝ) → 1 ≤ q.2.1 →
        ‖∑ s ∈ Finset.range (heightWindowCount H T),
          upperTailStoppedDyad i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨γ,hγ,huniform⟩ := angular_high_stopped_envelope_tail_uniform ℓ hpnt hMV hC hHuxley
  let κ₀ := γ/(100*(3+γ))
  have hden : 0 < 100*(3+γ) := by positivity
  have hκ₀ : 0 < κ₀ := div_pos hγ hden
  have hκ₀small : κ₀ < 1/12 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hκeq : κ₀*(3+γ) = γ/100 := by dsimp [κ₀]; field_simp
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle
  have hκsmall : κ < 1/12 := hκle.trans_lt hκ₀small
  have hmul := mul_le_mul_of_nonneg_right hκle (show 0 ≤ 3+γ by positivity)
  have hmargin : 1 < (1/3-κ)*(3+γ) := by nlinarith
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  let M : ℝ := ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform M hM n primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth
  refine ⟨K*(16:ℝ)^(5/6:ℝ)*4^n,by positivity,?_⟩
  filter_upwards [eventually_upperTailStoppedDyad_geometry hκ hρ hρ₂ hε hsmall hgap,
    eventually_upper_stopped_analytic_range hκ hκsmall hmargin,
    eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < 1/3-κ by linarith)).eventually_ge_atTop Z₀]
    with X hgeom hrange hX hlarge
  intro H T d q j k hT hH hHX hk
  have hXp : 0 < X := zero_lt_one.trans hX
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
  by_cases hz : (∑ s ∈ Finset.range (heightWindowCount H T),
      upperTailStoppedDyad i ℓ κ ρ ξ H (T*(3/2:ℝ)^s) X d q j k) = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨s,_hs,hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨hBlo,hBhi,hprodlo,hprodhi⟩ := hgeom i ℓ H (T*(3/2:ℝ)^s) d q j k hk hs
  let A := stoppedNormDyadLength j/2
  let B := stoppedNormDyadLength k
  have hAp : 0 < A := by dsimp [A]; positivity [stoppedNormDyadLength_pos j]
  have hBp : 0 < B := stoppedNormDyadLength_pos k
  have hB1 : 1 ≤ B :=
    (Real.one_le_rpow hX.le (show 0 ≤ 1/3-κ by linarith)).trans hBlo
  obtain ⟨hAlow,hAhigh,hA3,hBT,hHB3,hlog⟩ := hrange A B hprodlo hprodhi hBlo hBhi
  have hP (a : Eisenstein) (ha : a ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary a ∧ Squarefree a ∧ 1 ≤ norm a/A ∧ norm a/A ≤ 2 := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
    have hn := stoppedNormDyad_outer_bounds ha hp.1
    refine ⟨hp.1,hp.2.1,(one_le_div hAp).mpr hn.1,?_⟩
    apply (div_le_iff₀ hAp).mpr
    dsimp [A]
    nlinarith [hn.2]
  have hQ (b : Eisenstein) (hb : b ∈ stoppedNormDyad (distinguishedStoppedSide X) k) :
      primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp hb).1
    have hn := stoppedNormDyad_outer_bounds hb hp.1
    exact ⟨hp.1,hp.2.1,hn.1,hn.2⟩
  have hb := hbound (centralPrimaryFactors X) (centralPrimaryFactors X)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppedNormDyad (distinguishedStoppedSide X) k)
    primeDetectorCutoff (X^ξ) B A X T H (distinguishedScaleCoefficient i ξ X d)
    (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.1
      0 (X^(1/3-κ)) (X^(1/3-κ)) true)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)
    (fun _ hm => (mem_primaryElementBall.mp hm).1)
    (fun _ hm => (mem_primaryElementBall.mp hm).1)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (fun a _ => distinguishedScaleCoefficient_norm i ξ X d a)
    (hlarge.trans hBlo) hAlow hAhigh hA3 hXp (hBT.trans hT) hH (hHX.trans hHB3) hP hQ
  rw [angular_upperTailStoppedDyads_envelope ℓ i κ ρ ξ H T hXp d q j k]
  apply hb.trans
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hdenom : (1+Real.log X)^n ≤ (4:ℝ)^n*(1+Real.log B)^n := by
    have hh : 1+Real.log X ≤ 4*(1+Real.log B) := by linarith
    simpa only [mul_pow] using pow_le_pow_left₀ hLX.le hh n
  have hscale : A^(5/6:ℝ)*B^(5/6:ℝ) ≤ (16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ) := by
    rw [←Real.mul_rpow hAp.le hBp.le,←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hXp.le]
    exact Real.rpow_le_rpow (mul_nonneg hAp.le hBp.le) hprodhi (by norm_num)
  apply (div_le_div_iff₀ (pow_pos hLB n) (pow_pos hLX n)).mpr
  calc
    (K*A^(5/6:ℝ)*B^(5/6:ℝ))*(1+Real.log X)^n ≤
        (K*((16:ℝ)^(5/6:ℝ)*X^(5/6:ℝ)))*((4:ℝ)^n*(1+Real.log B)^n) := by
      apply mul_le_mul _ hdenom (pow_nonneg hLX.le n) (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hscale hK.le
    _ = _ := by ring


theorem angular_upperStoppedEnvelopeTail_bounds_uniform (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/12 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ i n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ),
        X^(1/100:ℝ) ≤ T → 1 ≤ H → H ≤ X^(1/2:ℝ) →
        ‖angular_upperStoppedEnvelopeTail ℓ i κ ρ ξ H T X‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hbound⟩ := angular_upperStoppedTail_bound_uniform ℓ hpnt hMV hC hHuxley
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle
  have hκsmall : κ < 1/12 := hκle.trans_lt hκ₀small
  have hbound := hbound κ hκ hκle
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  obtain ⟨K,hK,hpiece⟩ := hbound ρ ξ ε hρ hρ₂ hε hsmall hgap i (i+5+n)
  obtain ⟨D,hD,hagg⟩ := angular_upperStoppedEnvelopeTail_aggregate ℓ i hρ
  refine ⟨D*K,by positivity,?_⟩
  filter_upwards [hpiece,eventually_ge_atTop (1:ℝ)] with X hb hX
  intro H T hT hH hHX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hs := hagg κ ξ H T X hX (K*X^(5/6:ℝ)/(1+Real.log X)^(i+5+n))
    (by positivity) (fun d q hq j k => hb H T d q j k hT hH hHX
      (Finset.mem_filter.mp hq).2)
  apply hs.trans_eq
  rw [pow_add]
  field_simp
  simp only [pow_add]
  ring


theorem angular_upperStoppedFilteredArity_bounds_uniform (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/12 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ i n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (H T : ℝ),
        Real.log X ≤ T → 1 ≤ H → H ≤ X^(1/2:ℝ) →
        ‖angular_upperStoppedFilteredArity ℓ i κ ρ ξ H T X‖ ≤
          K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hbound⟩ := angular_upperStoppedEnvelopeTail_bounds_uniform ℓ hpnt hMV hC hHuxley
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle
  have hκsmall : κ < 1/12 := hκle.trans_lt hκ₀small
  have hbound := hbound κ hκ hκle
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  obtain ⟨K,hK,hb⟩ := hbound ρ ξ ε hρ hρ₂ hε hsmall hgap i n
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with X hb hX
  intro H T hT hH hHX
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hTp : 0 < T := (Real.log_pos hX).trans_le hT
  obtain ⟨j,hj,hstart,he⟩ := angular_upperStoppedFilteredArity_suffix ℓ i κ ρ ξ H T X hHp hTp
  by_cases hjN : j < heightWindowCount H T
  · rw [he]
    exact hb H (T*(3/2:ℝ)^j) (hstart hjN).le hH hHX
  · have hcount : heightWindowCount H (T*(3/2:ℝ)^j) = 0 := by
      rw [heightWindowCount_shift hHp hTp]
      omega
    rw [he,←angular_upperStoppedWindow_sum ℓ]
    simp only [hcount,Finset.range_zero,Finset.sum_empty,norm_zero]
    have hL : 0 < 1+Real.log X := by linarith [Real.log_pos hX]
    positivity


theorem angular_upperStoppedFilteredTail_isLittleO_uniform (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/12 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ (ρ ξ ε : ℝ),
      1 < ρ → ρ ≤ 2 → 0 ≤ ε → ρ ≤ (2:ℝ)^ε → ξ+ε < κ/2 →
      ∀ (m : ℕ) (H T : ℝ → ℝ),
        (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
        (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
        (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/2:ℝ)) →
        (fun X => ∑ i ∈ Finset.range m, angular_upperStoppedFilteredArity ℓ i κ ρ ξ (H X) (T X) X)
          =o[atTop] firstMomentScale := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hbound⟩ := angular_upperStoppedFilteredArity_bounds_uniform ℓ hpnt hMV hC hHuxley
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle
  have hκsmall : κ < 1/12 := hκle.trans_lt hκ₀small
  have hbound := hbound κ hκ hκle
  intro ρ ξ ε hρ hρ₂ hε hsmall hgap m H T hT hH hHX
  apply Asymptotics.IsLittleO.fun_sum
  intro i _hi
  obtain ⟨K,hK,hb⟩ := hbound ρ ξ ε hρ hρ₂ hε hsmall hgap i 3
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hb,hT,hH,hHX,eventually_ge_atTop (1:ℝ)] with X hb hT hH hHX hX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  simpa only [Real.norm_of_nonneg (by positivity :
    0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3),mul_div_assoc] using hb (H X) (T X) hT hH hHX


theorem angular_upperLowTail_isLittleO_uniform (hℓ : ℓ ≠ 0) (hpnt : PrimaryPrimePNT) {C : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ m : ℕ,
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2))) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < 1/12 ∧
      ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ξ : ℝ, 0 < ξ → ξ < κ/2 →
      ∀ m : ℕ, ∃ η : ℝ, 0 < η ∧ η ≤ κ/4 ∧ ∀ H T : ℝ → ℝ,
        (∀ᶠ X : ℝ in atTop, Real.log X ≤ T X) →
        (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
        (∀ᶠ X : ℝ in atTop, H X ≤ X^(1/6+η/2)) →
        (fun X => angular_upperLowTail ℓ m κ ξ (H X) (T X) X) =o[atTop] firstMomentScale := by
  obtain ⟨κ₀,hκ₀,hκ₀small,hstop⟩ := angular_upperStoppedFilteredTail_isLittleO_uniform ℓ hpnt hMV hC hHuxley
  refine ⟨κ₀,hκ₀,hκ₀small,?_⟩
  intro κ hκ hκle
  have hκsmall : κ < 1/12 := hκle.trans_lt hκ₀small
  have hstop := hstop κ hκ hκle
  intro ξ _hξ hξsmall m
  let η := κ/8
  let ε := (κ/2-ξ)/2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηκ : η ≤ κ/4 := by dsimp [η]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : ξ+ε < κ/2 := by dsimp [ε]; linarith
  have hcap : 1 < (2:ℝ)^ε := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨ρ,hρ,hρ₂,hsmall,hno⟩ := angular_upperNoStopTail_isLittleO ℓ hℓ m hpnt hVor hMV hC hGamma hκ hκsmall hη hηκ hcap
  refine ⟨η,hη,hηκ,?_⟩
  intro H T hT hH hHX
  have hsetup : ∀ᶠ X : ℝ in atTop,
      1 ≤ H X ∧ H X ≤ X^(1/6+η/2) ∧ Real.log X ≤ T X := by
    filter_upwards [hT,hH,hHX] with X ht hh hx
    exact ⟨hh,hx,ht⟩
  have hHhalf : ∀ᶠ X : ℝ in atTop, H X ≤ X^(1/2:ℝ) := by
    filter_upwards [hHX,eventually_ge_atTop (1:ℝ)] with X hx hX
    exact hx.trans (Real.rpow_le_rpow_of_exponent_le hX (by dsimp [η]; linarith))
  have hsum := (hno ξ H T hsetup).add
    (hstop ρ ξ ε hρ hρ₂ hε.le hsmall hgap m H T hT hH hHhalf)
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [angular_upperLowTail_stopping ℓ m ξ hκ] with X hid
  exact (hid ρ hρ hρ₂ (H X) (T X)).symm


end CubicFirstMoment

end

end OAI
