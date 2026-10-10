import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonSquareDivisor
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonPowers

namespace OAI

/-! All nonunit common factors of an active rough coefficient are restored.
The three explicit costs are the rough small factors, the power-saving
large factors, and their exact zero mode. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_rough_common_remainder (hpnt : PrimaryPrimePNT)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (j : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A M u R D : ℝ), 2 < Z → Z^(3/2:ℝ) ≤ A → 0 ≤ M → 0 < R →
      1 ≤ D → D ≤ Z^(1/1000:ℝ) → D^4 ≤ R →
      65536*(Z/2)^(1/4:ℝ) ≤ Z →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ Z/2 ≤ norm a ∧ norm a ≤ Z) →
      (∀ a ∈ S, ‖β a‖ ≤ M) →
      (∀ a ∈ S, β a ≠ 0 → ∀ p, primaryPrime p → p ∣ a → R ≤ norm p) →
      ‖∑ k ∈ (commonRowFactors S).filter (fun k => k ≠ 1),
        commonGramBlock S (fun a => star (dispersionAmplitude β u a)) V (A/D^2) k‖ ≤
      K*(A^(2/3:ℝ)*Z^(5/3:ℝ)*(1+Real.log Z)^j*R^(-(1/6:ℝ))+
        A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)+A*Z)*M^2 := by
  obtain ⟨Ks,j,hKs,hsmall⟩ := rough_square_divisor_common_blocks hpnt hHuxley V hV hV'
  obtain ⟨Kl,hKl,hlarge⟩ := bounded_large_common_nonzero V hV hV'
  let c : ℝ := 18*(‖normProfileFourier V 0‖/9)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let K : ℝ := Ks+Kl+c+1
  refine ⟨K,j,by dsimp [K]; positivity,?_⟩
  intro S β Z A M u R D hZ hA hM hR hD hDhi hDR hcut hS hβ hrough
  have hZ1 : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hAp : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hA'p : 0 < A/D^2 := by positivity
  have hAle : A/D^2 ≤ A := div_le_self hAp.le (one_le_pow₀ hD)
  have hS₀ : ∀ a ∈ S, primary a ∧ Squarefree a := fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩
  let v : Eisenstein → ℂ := fun a => star (dispersionAmplitude β u a)
  let F := commonRowFactors S
  let H := (Z/2)^(1/4:ℝ)
  let I := F.filter (fun k => norm k < H ∧ k ≠ 1)
  let J := F.filter (fun k => H ≤ norm k)
  let G := ∑ k ∈ I, commonGramBlock S v V (A/D^2) k
  let L := ∑ k ∈ J, (commonGramBlock S v V (A/D^2) k-commonGramZeroMode S v V (A/D^2) k)
  let Q := ∑ k ∈ J, commonGramZeroMode S v V (A/D^2) k
  let U := A^(2/3:ℝ)*Z^(5/3:ℝ)*(1+Real.log Z)^j*R^(-(1/6:ℝ))
  let W := A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)
  have hlog : 0 ≤ 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hG : ‖G‖ ≤ Ks*U*M^2 := by
    have hb := hsmall S I β Z A M u R D hZ1 hA hM hR hD hDR
      (fun k hk => by
        have hki := Finset.mem_filter.mp hk
        have hp := commonRowFactors_spec hS₀ hki.1
        exact ⟨hp.1,hp.2,hki.2.2,rough_common_small_quotient
          (norm_pos_of_ne_zero (primary_ne_zero hp.1)) hcut hki.2.1⟩) hS hβ hrough
    exact hb.trans_eq (by dsimp [U]; ring)
  have hL : ‖L‖ ≤ Kl*W*M^2 := by
    have hb := hlarge S β Z (A/D^2) M u (by linarith) hA'p
      (rough_common_large_outer (by linarith) hDp hDhi hA) hS hβ
    apply hb.trans
    have hs := Real.rpow_le_rpow hA'p.le hAle (by norm_num : (0:ℝ) ≤ 2/3)
    calc
      _ ≤ Kl*A^(2/3:ℝ)*Z^(5/3-1/32:ℝ)*M^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs hKl.le) (Real.rpow_nonneg hZp.le _)) (sq_nonneg M)
      _ = _ := by dsimp [W]; ring
  have hQ : ‖Q‖ ≤ c*(A*Z)*M^2 := by
    have hv (a : Eisenstein) (ha : a ∈ S) : ‖v a‖ ≤ M := by
      simpa only [v,norm_star,dispersionAmplitude_norm_squarefree (hS a ha).1 (hS a ha).2.1]
        using hβ a ha
    have he := bounded_coefficient_energy S v hZp.le
      (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2.2⟩) hv
    have hb := commonGramZeroMode_sum_bound S J hS₀
      (fun k hk => commonRowFactors_spec hS₀ (Finset.mem_filter.mp hk).1) v V hA'p.le
    apply hb.trans
    calc
      _ ≤ (‖normProfileFourier V 0‖/9)*A*(18*Z*M^2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAle (by positivity)) he
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
      _ = _ := by dsimp [c]; ring
  have hH : 1 < H := Real.one_lt_rpow (by linarith) (by norm_num)
  have he : (∑ k ∈ F.filter (fun k => k ≠ 1), commonGramBlock S v V (A/D^2) k) = G+L+Q := by
    dsimp only [G,L,Q,I,J]
    rw [add_assoc,←Finset.sum_add_distrib]
    simp only [sub_add_cancel,Finset.sum_filter]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk1 : k = 1
    · subst k
      simp only [ne_eq,not_true_eq_false,ite_false,and_false,norm_one_eq]
      rw [ite_eq_right (not_le.mpr hH)]
      simp
    · by_cases hkH : norm k < H
      · simp only [hk1,ne_eq,not_false_eq_true,hkH,and_self,ite_true,
          not_le.mpr hkH,ite_false,add_zero]
      · simp only [hk1,ne_eq,not_false_eq_true,hkH,false_and,ite_false,
          le_of_not_gt hkH,ite_true,zero_add]
  change ‖∑ k ∈ F.filter (fun k => k ≠ 1), commonGramBlock S v V (A/D^2) k‖ ≤ _
  rw [he]
  apply ((norm_add_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add hG hL)) hQ))).trans
  have hKsK : Ks ≤ K := by dsimp [K]; linarith
  have hKlK : Kl ≤ K := by dsimp [K]; linarith
  have hcK : c ≤ K := by dsimp [K]; linarith
  calc
    _ ≤ K*U*M^2+K*W*M^2+K*(A*Z)*M^2 := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKsK hU) (sq_nonneg M))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKlK hW) (sq_nonneg M)))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcK (mul_nonneg hAp.le hZp.le))
          (sq_nonneg M))
    _ = _ := by dsimp [U,W]; ring

end CubicFirstMoment

end

end OAI
