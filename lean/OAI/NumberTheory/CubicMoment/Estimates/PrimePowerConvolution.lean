import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerBalanced
import OAI.NumberTheory.CubicMoment.Estimates.FirstShapeErrorMoment

namespace OAI

/-! Actual prime-power convolution coefficients: bounded prime support absorbs
all tuple multiplicities in an arbitrarily small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_eq_zero_of_not_mem (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {b : Eisenstein}
    (hb : b ∉ orderedConvolutionSupport S) : orderedConvolution S w b = 0 := by
  unfold orderedConvolution
  apply Finset.sum_eq_zero
  intro f hf
  obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
  exact False.elim (hb (Finset.mem_image.mpr ⟨f,hfs,hfb⟩))

/-- A tuple with prescribed nonzero product chooses each coordinate among
its primary divisors. Boundedly many prime bases give a logarithmic bound. -/
theorem primePower_tuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, ∃ p : Eisenstein, ∃ j : ℕ,
      primaryPrime p ∧ 0 < j ∧ a = p^j) (b : Eisenstein) :
    ((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card ≤
      (Nat.log 2 (normNat b)+1)^((Fintype.card ι)*(Fintype.card ι)) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  by_cases ht : T.Nonempty
  · obtain ⟨f,hf⟩ := ht
    obtain ⟨hfs,hfb⟩ := Finset.mem_filter.mp hf
    have hb : b ∈ orderedConvolutionSupport S :=
      Finset.mem_image.mpr ⟨f,hfs,hfb⟩
    obtain ⟨hbprim,hbk⟩ := orderedPrimePowerSupport_spec S hS hb
    have hprimary : ∀ i, ∀ a ∈ S i, primary a := by
      intro i a ha
      obtain ⟨p,j,hp,_,rfl⟩ := hS i a ha
      simpa using primary_finset_prod (Finset.range j) (fun _ => p) (fun _ _ => hp.1)
    have hsub : T ⊆ Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b)) := by
      intro g hg
      obtain ⟨hgs,hgb⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      intro i
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hgs i,?_⟩
      rw [← hgb]
      exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)
    calc
      T.card ≤ (Fintype.piFinset (fun i => (S i).filter (fun a => a ∣ b))).card :=
        Finset.card_le_card hsub
      _ = ∏ i, ((S i).filter (fun a => a ∣ b)).card := Fintype.card_piFinset _
      _ ≤ ∏ _i : ι, (Nat.log 2 (normNat b)+1)^(Fintype.card ι) :=
        Finset.prod_le_prod (fun i _ => primary_divisor_card_log (S i) (hprimary i)
          (primary_ne_zero hbprim) hbk)
      _ = _ := by simp [← pow_mul]
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- Actual independent weights, including arbitrary higher prime powers. -/
theorem primePower_orderedConvolution_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ a ∈ S i, ∃ p : Eisenstein, ∃ j : ℕ,
      primaryPrime p ∧ 0 < j ∧ a = p^j)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b‖ ≤
      (((Nat.log 2 (normNat b)+1)^((Fintype.card ι)*(Fintype.card ι)):ℕ):ℝ)*(∏ i, M i) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun i _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (primePower_tuple_fiber_card S hS b))
      (Finset.prod_nonneg (fun i _ => hM i))

/-- The full coefficient multiplicity has arbitrary small-power growth,
uniformly in the separate prime-power supports and weights. -/
theorem primePower_orderedConvolution_smallPower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, ∃ p : Eisenstein, ∃ j : ℕ,
        primaryPrime p ∧ 0 < j ∧ a = p^j) →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (Y : ℝ), 1 ≤ Y → ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖orderedConvolution S w b‖ ≤ C*Y^ε*(∏ i, M i) := by
  obtain ⟨C,hC,hbound⟩ := natLog_power_bound ((Fintype.card ι)*(Fintype.card ι)) hε
  refine ⟨C,hC,?_⟩
  intro S w M hS hM hw Y hY b hb hnorm
  obtain ⟨hbprim,_⟩ := orderedPrimePowerSupport_spec S hS hb
  have hn : 1 ≤ normNat b := Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero hbprim))
  have hnY : (normNat b:ℝ) ≤ Y := (normNat_cast b).trans_le hnorm
  have hp : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  apply (primePower_orderedConvolution_norm_bound S w M hS hM hw b).trans
  apply mul_le_mul_of_nonneg_right _ hp
  push_cast
  simpa only [Nat.cast_add, Nat.cast_one] using
    (hbound (normNat b) hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnY hε.le) hC.le)

/-- Actual collected higher-prime-power coefficients on the sparse error
support satisfy the balanced moment. The only analytic input is Huxley. -/
theorem primePowerConvolution_balanced_second_moment
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, ∃ p : Eisenstein, ∃ j : ℕ,
        primaryPrime p ∧ 0 < j ∧ a = p^j) →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ Y : ℝ, 1 ≤ Y → ∀ P : Finset (Eisenstein × Eisenstein),
      (∀ p ∈ P, PrimarySquarefreePair p ∧
        norm p.1 ≤ Y^(1/3+c/128) ∧ norm p.2 ≤ Y^(1/3+c/128)) →
      ∀ χ : Eisenstein → ℂ,
      (∀ b ∈ (orderedConvolutionSupport S).filter
        (fun b => b ∈ largePrimePowerSupport Y c), ‖χ b‖ ≤ 1) →
      (∑ p ∈ P, ‖∑ b ∈ (orderedConvolutionSupport S).filter
        (fun b => b ∈ largePrimePowerSupport Y c),
        (orderedConvolution S w b*χ b)*mixedCubic p.1 p.2 b‖^2) ≤
      C*(∏ i, M i)^2*Y^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primePower_balanced_second_moment hHuxley (Fintype.card ι) hc hc₁
  obtain ⟨D,hD,hcoeff⟩ := primePower_orderedConvolution_smallPower
    (ι := ι) (show 0 < c/64 by positivity)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro S w M hS hM hw Y hY P hP χ hχ
  let B := (orderedConvolutionSupport S).filter (fun b => b ∈ largePrimePowerSupport Y c)
  have hB : ∀ b ∈ B, primary b ∧ (idealExponentOf b).support.card ≤ Fintype.card ι :=
    fun b hb => orderedPrimePowerSupport_spec S hS (Finset.mem_filter.mp hb).1
  have hsub : B ⊆ largePrimePowerSupport Y c := fun _ hb => (Finset.mem_filter.mp hb).2
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have hA : ∀ b ∈ B, ‖orderedConvolution S w b*χ b‖ ≤ D*Y^(c/64)*(∏ i, M i) := by
    intro b hb
    have hnorm := (mem_nonzeroNormBall.mp (Finset.mem_filter.mp (hsub hb)).1).1
    rw [norm_mul]
    calc
      _ ≤ ‖orderedConvolution S w b‖*1 := mul_le_mul_of_nonneg_left (hχ b hb) (_root_.norm_nonneg _)
      _ ≤ _ := by
        simpa only [mul_one] using hcoeff S w M hS hM hw Y hY b
          (Finset.mem_filter.mp hb).1 hnorm
  have h := hbound Y (D*Y^(c/64)*(∏ i, M i)) hY (by positivity)
    B hB hsub P hP (fun b => orderedConvolution S w b*χ b) hA
  have hY0 : 0 < Y := by linarith
  have hp : (Y^(c/64))^2*Y^(7/3-c/16) = Y^(7/3-c/32) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le,← Real.rpow_add hY0]
    congr 1
    ring
  calc
    _ ≤ C*(D*Y^(c/64)*(∏ i, M i))^2*Y^(7/3-c/16) := h
    _ = (C*D^2)*(∏ i, M i)^2*((Y^(c/64))^2*Y^(7/3-c/16)) := by ring
    _ = _ := by rw [hp]

/-- The first exceptional shape for the same actual prime-power convolution.
The collected coefficient automatically vanishes outside its tuple support. -/
theorem primePowerConvolution_first_shape_second_moment
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, ∃ p : Eisenstein, ∃ j : ℕ,
        primaryPrime p ∧ 0 < j ∧ a = p^j) →
      (∀ i, 0 ≤ M i) → (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ Y : ℝ, 1 ≤ Y → ∀ P Q : Finset Eisenstein,
      (∀ p ∈ P, primary p ∧ Squarefree p ∧ norm p ≤ Y^(1+c/128)) →
      (∀ q ∈ Q, primary q ∧ norm q ≤ Y^(c/128)) →
      ∀ χ : Eisenstein → ℂ,
      (∀ b ∈ largePrimePowerSupport Y c, ‖χ b‖ ≤ 1) →
      (∑ q ∈ Q, ∑ p ∈ P, ‖∑ b ∈ largePrimePowerSupport Y c,
        (orderedConvolution S w b*χ b)*mixedCubic p q b‖^2) ≤
      C*(∏ i, M i)^2*Y^(7/3-c/32) := by
  obtain ⟨C,hC,hbound⟩ := primePower_first_shape_second_moment hc hc₁
  obtain ⟨D,hD,hcoeff⟩ := primePower_orderedConvolution_smallPower
    (ι := ι) (show 0 < c/64 by positivity)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro S w M hS hM hw Y hY P Q hP hQ χ hχ
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have hA : ∀ b ∈ largePrimePowerSupport Y c,
      ‖orderedConvolution S w b*χ b‖ ≤ D*Y^(c/64)*(∏ i, M i) := by
    intro b hb
    by_cases hbS : b ∈ orderedConvolutionSupport S
    · have hnorm := (mem_nonzeroNormBall.mp (Finset.mem_filter.mp hb).1).1
      rw [norm_mul]
      calc
        _ ≤ ‖orderedConvolution S w b‖*1 :=
          mul_le_mul_of_nonneg_left (hχ b hb) (_root_.norm_nonneg _)
        _ ≤ _ := by
          simpa only [mul_one] using hcoeff S w M hS hM hw Y hY b hbS hnorm
    · rw [orderedConvolution_eq_zero_of_not_mem S w hbS,zero_mul,norm_zero]
      positivity
  have h := hbound Y (D*Y^(c/64)*(∏ i, M i)) hY (by positivity)
    P Q hP hQ (fun b => orderedConvolution S w b*χ b) hA
  have hY0 : 0 < Y := by linarith
  have hp : (Y^(c/64))^2*Y^(7/3-c/16) = Y^(7/3-c/32) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le,← Real.rpow_add hY0]
    congr 1
    ring
  calc
    _ ≤ C*(D*Y^(c/64)*(∏ i, M i))^2*Y^(7/3-c/16) := h
    _ = (C*D^2)*(∏ i, M i)^2*((Y^(c/64))^2*Y^(7/3-c/16)) := by ring
    _ = _ := by rw [hp]

end CubicFirstMoment

end

end OAI
