import OAI.NumberTheory.CubicMoment.Estimates.PrimaryConvolutionEnergy
import OAI.NumberTheory.CubicMoment.Estimates.PrimePowerMoments
import OAI.NumberTheory.CubicGram.InnerExtension

namespace OAI

/-! The sharp bounded-coefficient cubic sieve, specialized to actual
primary convolutions. The pointwise divisor bound is essential here. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma finite_polynomial_dyad_partition (H : Finset Eisenstein)
    (hH : ∀ n ∈ H, n ≠ 0) (v : Eisenstein → ℂ) (a : Eisenstein) :
    (∑ n ∈ H, v n*cubicSymbol a n) =
      ∑ j ∈ H.image (fun n => Nat.log 2 (normNat n)),
        ∑ n ∈ frequencyDyad j, (if n ∈ H then v n else 0)*cubicSymbol a n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun n hn => Finset.mem_image_of_mem (fun n => Nat.log 2 (normNat n)) hn)]
  apply Finset.sum_congr rfl
  intro j hj
  have hsub : H.filter (fun n => Nat.log 2 (normNat n) = j) ⊆ frequencyDyad j := by
    intro n hn
    exact mem_frequencyDyad.mpr ⟨hH n (Finset.mem_filter.mp hn).1,(Finset.mem_filter.mp hn).2⟩
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [(Finset.mem_filter.mp hn).1,ite_true]
  · intro n hn hnot
    have hnH : n ∉ H := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨h,(mem_frequencyDyad.mp hn).2⟩)
    simp [hnH]

/-- Sharp cutoff form of the proved bounded-coefficient inner extension.
The coefficient support may contain cubes and need not be squarefree. -/
theorem bounded_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : Finset Eisenstein) (N Y D : ℝ),
      1 ≤ N → 1 ≤ Y → 0 ≤ D →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ n ∈ H, n ≠ 0 ∧ norm n ≤ Y) → ∀ v : Eisenstein → ℂ,
      (∀ n ∈ H, ‖v n‖ ≤ D) →
      (∑ a ∈ P, ‖∑ n ∈ H, v n*cubicSymbol a n‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*D^2 := by
  obtain ⟨C,hC,hdyad⟩ := cubic_inner_extension (show 0 < ε/2 by linarith)
  obtain ⟨E,hE,hlog⟩ := natLog_power_bound 2 (show 0 < ε/2 by linarith)
  refine ⟨C*E,mul_pos hC hE,?_⟩
  intro P H N Y D hN hY hD hP hH v hv
  let J := H.image (fun n => Nat.log 2 (normNat n))
  let w : Eisenstein → ℂ := fun n => if n ∈ H then v n else 0
  let F : ℝ := N+Y+(N*Y)^(2/3:ℝ)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hcount : (J.card:ℝ)^2 ≤ E*Y^(ε/2) := by
    have hsub : J ⊆ Finset.range (Nat.log 2 ⌊Y⌋₊+1) := by
      intro j hj
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_range.mpr
      have hnY : normNat n ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa only [normNat_cast] using (hH n hn).2)
      exact Nat.lt_succ_of_le (Nat.log_mono_right hnY)
    calc
      _ ≤ ((Nat.log 2 ⌊Y⌋₊+1:ℕ):ℝ)^2 := pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast (show J.card ≤ Nat.log 2 ⌊Y⌋₊+1 by
          simpa only [Finset.card_range] using Finset.card_le_card hsub)) _
      _ ≤ E*(⌊Y⌋₊:ℝ)^(ε/2) := hlog _ ((Nat.one_le_floor_iff Y).mpr hY)
      _ ≤ E*Y^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY0.le) (by positivity)) hE.le
  have hrow (j : ℕ) (hj : j ∈ J) :
      (∑ a ∈ P, ‖∑ n ∈ frequencyDyad j, w n*cubicSymbol a n‖^2) ≤
        C*(N*Y)^(ε/2)*Y*F*D^2 := by
    obtain ⟨n,hn,hnj⟩ := Finset.mem_image.mp hj
    have hnD : n ∈ frequencyDyad j := mem_frequencyDyad.mpr ⟨(hH n hn).1,hnj⟩
    have hjY : (2:ℝ)^j ≤ Y := (frequencyDyad_norm hnD).1.trans (hH n hn).2
    have hw : ∀ n ∈ frequencyDyad j, ‖w n‖ ≤ D := by
      intro n _
      dsimp only [w]
      split_ifs with hn
      · exact hv n hn
      · simpa using hD
    apply (hdyad P N hN hP j w D hD hw).trans
    dsimp only [F]
    gcongr
  have hsplit (a : Eisenstein) : (∑ n ∈ H, v n*cubicSymbol a n) =
      ∑ j ∈ J, ∑ n ∈ frequencyDyad j, w n*cubicSymbol a n :=
    finite_polynomial_dyad_partition H (fun n hn => (hH n hn).1) v a
  simp_rw [hsplit]
  apply (complex_mass_sum_sq_le J P
    (fun a j => ∑ n ∈ frequencyDyad j, w n*cubicSymbol a n)).trans
  calc
    _ ≤ (J.card:ℝ)*∑ _j ∈ J, C*(N*Y)^(ε/2)*Y*F*D^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = (J.card:ℝ)^2*C*(N*Y)^(ε/2)*Y*F*D^2 := by simp; ring
    _ ≤ (E*Y^(ε/2))*C*(N*Y)^(ε/2)*Y*F*D^2 := by gcongr
    _ = (C*E)*(Y^(ε/2)*(N*Y)^(ε/2))*Y*F*D^2 := by ring
    _ ≤ (C*E)*(N*Y)^ε*Y*F*D^2 := by
      have he : Y^(ε/2)*(N*Y)^(ε/2) ≤ (N*Y)^ε := by
        calc
          _ ≤ (N*Y)^(ε/2)*(N*Y)^(ε/2) := by
            gcongr
            exact le_mul_of_one_le_left hY0.le hN
          _ = _ := by rw [← Real.rpow_add (mul_pos hN0 hY0)]; congr 1; ring
      gcongr

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise coefficient bound for the actual independent primary
convolution, uniform in its supports and independent factor weights. -/
theorem primary_orderedConvolution_norm {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b ∈ orderedConvolutionSupport S, norm b ≤ Y →
      ‖orderedConvolution S w b‖ ≤ C*Y^δ*(∏ i, M i) := by
  obtain ⟨C,hC,hfiber⟩ := primary_tuple_fiber_small_power (ι := ι) hδ
  refine ⟨C,hC,?_⟩
  intro S w M hS hM hw Y hY b hb hbY
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1 i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hfiber S hS Y hY b hb hbY)
      (Finset.prod_nonneg (fun i _ => hM i))

/-- Sharp cubic moment for the actual collected primary convolution,
including any fixed coefficient twist of norm at most one. -/
theorem primaryConvolution_sharp_twisted_moment {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P : Finset Eisenstein) (N Y : ℝ), 1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      (∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        (orderedConvolution S w b*χ b)*cubicSymbol a b‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*(Y^δ*(∏ i, M i)^2) := by
  obtain ⟨C,hC,hbound⟩ := bounded_cubic_moment hε
  obtain ⟨D,hD,hnorm⟩ := primary_orderedConvolution_norm (ι := ι)
    (show 0 < δ/2 by linarith)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro S w M hS hM hw P N Y hN hY hP hprod χ hχ
  have hMprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    refine ⟨primary_ne_zero (orderedPrimarySupport_primary S hS hb),?_⟩
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    exact hprod f hf
  have h := hbound P (orderedConvolutionSupport S) N Y (D*Y^(δ/2)*(∏ i, M i))
    hN hY (by positivity) hP hH (fun b => orderedConvolution S w b*χ b) (by
      intro b hb
      rw [norm_mul]
      exact (mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ b hb)).trans
        (hnorm S w M hS hM hw Y hY b hb (hH b hb).2))
  have hpow : (Y^(δ/2))^2 = Y^δ := by
    rw [← Real.rpow_mul_natCast (by linarith)]
    congr 1
    norm_num
  simpa only [mul_pow,hpow,mul_assoc,mul_left_comm,mul_comm] using h

/-- The untwisted product polynomial has the same sharp moment; every
factor is permitted to be an arbitrary primary-element polynomial. -/
theorem primaryConvolution_sharp_product_moment {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) →
      ∀ (P : Finset Eisenstein) (N Y : ℝ), 1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*(Y^δ*(∏ i, M i)^2) := by
  obtain ⟨C,hC,hbound⟩ := primaryConvolution_sharp_twisted_moment (ι := ι) hε hδ
  refine ⟨C,hC,?_⟩
  intro S w M hS hM hw P N Y hN hY hP hprod
  have h := hbound S w M hS hM hw P N Y hN hY hP hprod (fun _ => 1) (by simp)
  have he : (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) =
      ∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        (orderedConvolution S w b*1)*cubicSymbol a b‖^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mul_one,primeCubicProductPolynomial_eq S w (hP a ha).1]
  rw [he]
  exact h

end CubicFirstMoment

end

end OAI
