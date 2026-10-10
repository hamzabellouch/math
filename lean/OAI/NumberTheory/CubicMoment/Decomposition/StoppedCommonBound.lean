import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonPointwise
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonTail

namespace OAI

/-! The pointwise bounded-row estimate summed over its actual Möbius
expansion and over rough common factors. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem bounded_common_block_at_scale (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u : ℝ) (k : Eisenstein),
      0 ≤ Z → 0 < A → 0 ≤ M → primary k → Squarefree k →
      65536 ≤ Z/norm k → (Z/norm k)^(3/2:ℝ) ≤ A/norm k →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d*
          ((2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) := by
  obtain ⟨K,d,hK,hrow⟩ := bounded_common_coprime_row_at_scale hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S β Z A M u k hZ hA0 hM hk hks hres hscaleK hS hβ
  have hk1 := one_le_norm (primary_ne_zero hk)
  have hres1 : 1 ≤ Z/norm k := by linarith
  have hS₀ : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  let W := K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d*norm k^(-(5/3:ℝ))
  have hb (s : Finset Eisenstein) (hs : s ∈ (primaryPrimeFactors k).powerset) :
      ‖(idealMoebius (∏ p ∈ s,p):ℂ)*coprimeGramForm (residualRows S k)
        (commonBlockCoefficient (fun a => star (dispersionAmplitude β u a)) k (∏ p ∈ s,p))
        V (A/norm (∏ p ∈ s,p))‖ ≤ W := by
    have hsub := Finset.mem_powerset.mp hs
    have hm : primary (∏ p ∈ s,p) := primary_finset_prod _ _
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1.1)
    have hmk : (∏ p ∈ s,p) ∣ k := (primary_subsets_prod_dvd hk hsub k).mpr
      (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).2)
    rw [norm_mul]
    apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
    have hscaleM : (Z/norm k)^(3/2:ℝ) ≤ A/norm (∏ p ∈ s,p) :=
      hscaleK.trans (div_le_div_of_nonneg_left hA0.le
        (norm_pos_of_ne_zero (primary_ne_zero hm))
        (norm_le_of_dvd (primary_ne_zero hk) hmk))
    apply (hrow S β Z A M u k _ hM hk hm hres hscaleM hS hβ).trans
    have hscale := bounded_common_residual_scale d hA0.le hZ hk1
      (one_le_norm (primary_ne_zero hm)) hres1
    calc
      _ = (K*M^2)*((A/norm (∏ p ∈ s,p))^(2/3:ℝ)*(Z/norm k)^(5/3:ℝ)*
          (1+Real.log (Z/norm k))^d) := by ring
      _ ≤ (K*M^2)*(A^(2/3:ℝ)*Z^(5/3:ℝ)*norm k^(-(5/3:ℝ))*(1+Real.log Z)^d) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = W := by dsimp [W]; ring
  rw [commonGramBlock_moebius S hS₀ _ V hV hV' hA0 hk hks]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _s ∈ (primaryPrimeFactors k).powerset, W := Finset.sum_le_sum hb
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      dsimp [W]
      ring

theorem bounded_common_block (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u : ℝ) (k : Eisenstein),
      0 ≤ Z → Z^(3/2:ℝ) ≤ A → 0 ≤ M → primary k → Squarefree k →
      65536 ≤ Z/norm k →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d*
          ((2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) := by
  obtain ⟨K,d,hK,hbound⟩ := bounded_common_block_at_scale hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S β Z A M u k hZ hA hM hk hks hres hS hβ
  have hkp := norm_pos_of_ne_zero (primary_ne_zero hk)
  have hZp : 0 < Z := by
    have hz := (lt_div_iff₀ hkp).mp (show 0 < Z/norm k by linarith)
    simpa only [zero_mul] using hz
  exact hbound S β Z A M u k hZ ((Real.rpow_pos_of_pos hZp _).trans_le hA)
    hM hk hks hres
    (smallB_common_outer_scale hZ (one_le_norm (primary_ne_zero hk)) hkp le_rfl hA) hS hβ

theorem rough_common_blocks_at_scale (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S I : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u R : ℝ),
      1 ≤ Z → 0 < A → 0 ≤ M → 0 < R →
      (∀ k ∈ I, primary k ∧ Squarefree k ∧ R ≤ norm k ∧ 65536 ≤ Z/norm k ∧
        (Z/norm k)^(3/2:ℝ) ≤ A/norm k) →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖∑ k ∈ I, commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d*R^(-(1/6:ℝ)) := by
  obtain ⟨K,d,hK,hblock⟩ := bounded_common_block_at_scale hpnt hHuxley V hV hV'
  obtain ⟨C,hC,htail⟩ := rough_common_factor_weight_tail
  refine ⟨K*C,d,mul_pos hK hC,?_⟩
  intro S I β Z A M u R hZ hA hM hR hI hS hβ
  have hlog : 0 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hZ]
  let W := K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ ≤ ∑ k ∈ I, W*((2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk =>
        hblock S β Z A M u k (zero_le_one.trans hZ) hA hM
          (hI k hk).1 (hI k hk).2.1 (hI k hk).2.2.2.1 (hI k hk).2.2.2.2 hS hβ))
    _ = W*(∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ W*(C*R^(-(1/6:ℝ))) := mul_le_mul_of_nonneg_left
      (htail I R hR (fun k hk => ⟨(hI k hk).1,(hI k hk).2.2.1⟩)) hW
    _ = _ := by dsimp [W]; ring

theorem rough_common_blocks_bound (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S I : Finset Eisenstein)
      (β : Eisenstein → ℂ) (Z A M u R : ℝ),
      1 ≤ Z → Z^(3/2:ℝ) ≤ A → 0 ≤ M → 0 < R →
      (∀ k ∈ I, primary k ∧ Squarefree k ∧ R ≤ norm k ∧ 65536 ≤ Z/norm k) →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      ‖∑ k ∈ I, commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V A k‖ ≤
        K*A^(2/3:ℝ)*Z^(5/3:ℝ)*M^2*(1+Real.log Z)^d*R^(-(1/6:ℝ)) := by
  obtain ⟨K,d,hK,hbound⟩ := rough_common_blocks_at_scale hpnt hHuxley V hV hV'
  refine ⟨K,d,hK,?_⟩
  intro S I β Z A M u R hZ hA hM hR hI hS hβ
  apply hbound S I β Z A M u R hZ
    ((Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hA) hM hR
    _ hS hβ
  intro k hk
  have hp := (hI k hk).1
  exact ⟨hp,(hI k hk).2.1,(hI k hk).2.2.1,(hI k hk).2.2.2,
    smallB_common_outer_scale (zero_le_one.trans hZ)
      (one_le_norm (primary_ne_zero hp)) (norm_pos_of_ne_zero (primary_ne_zero hp)) le_rfl hA⟩

end CubicFirstMoment

end

end OAI
