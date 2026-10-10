import OAI.Probability.ContinuumTransition.LowerGibbs

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem kac_grandIntegral_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hS : 0 < S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    {q : ℕ} (hq : 0 < q) (hu : 2 ≤ (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ) (h : ℝ)
    (hF : GrandFinite (fixedOccupationFamily (innerGridBox ((q : ℝ)/4))
      (gridIndices (m+N) 1) (fun _ => n)
      (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β (t*h)))
      (⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k))
    (hG : GrandFinite
      (gibbsFamily (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) β (t*h))
      (cube (2*((m+N : ℕ)+1)*((q : ℝ)/4)))) :
    Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      grandIntegral (fixedOccupationFamily (innerGridBox ((q : ℝ)/4))
        (gridIndices (m+N) 1) (fun _ => n)
        (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β (t*h)))
        (⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k) ≤
      grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h
        (2*((m+N : ℕ)+1)*((q : ℝ)/4)) := by
  have hu0 : 0 < (q : ℝ)/4 := by positivity
  let D := ⋃ k ∈ gridIndices (m+N) 1, innerGridBox ((q : ℝ)/4) k
  let L := 2*((m+N : ℕ)+1)*((q : ℝ)/4)
  have hD : MeasurableSet D := MeasurableSet.biUnion (Finset.finite_toSet _).countable
    (fun k _ => measurableSet_innerGridBox _ k)
  have hsub : D ⊆ cube L := iUnion₂_subset (fun k hk => innerGridBox_subset_cube hu0.le hk)
  let F : ConfigFamily := fixedOccupationFamily (innerGridBox ((q : ℝ)/4))
    (gridIndices (m+N) 1) (fun _ => n)
    (gibbsFamily (quadraticBlock q (physicalProfile t σ R) 0) β (t*h))
  let G : ConfigFamily := gibbsFamily
    (fun x y => physicalProfile t (prepend a σ) (prepend S R) ‖x-y‖) β (t*h)
  let c : ℝ := Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)
  have hFc : GrandFinite (fun ι _ x => c*F ι x) D := hF.const_mul c
  have hGd : GrandFinite G D := hG.mono_set hsub (gibbsFamily_nonneg _ _ _)
  have hpoint : ∀ j (x : Fin j → Space), (∀ i, x i ∈ D) →
      c*F (Fin j) x ≤ G (Fin j) x := by
    intro j x hx
    exact kac_gibbsFamily_lower_fixed hC ht hβ ha hS hσ hR hs hq hu (m := m) hN n x hx
  have hb : grandIntegral (fun ι _ x => c*F ι x) D ≤ grandIntegral G D :=
    grandIntegral_mono (fun ι _ x => c*F ι x) G hD
      (fun j => hFc.integrable (Fin j)) (fun j => hGd.integrable (Fin j))
      hFc.summable hGd.summable hpoint
  have hb' := hb.trans (grandIntegral_mono_set _ hsub (gibbsFamily_nonneg _ _ _)
    (fun j => hG.integrable (Fin j)) hGd.summable hG.summable)
  rw [grandIntegral_const_mul] at hb'
  change c*grandIntegral F D ≤ grandIntegral G (cube L) at hb'
  rw [show grandIntegral G (cube L) = grandPartition (physicalProfile t (prepend a σ)
      (prepend S R)) t β h L from grandIntegral_radial _ _ _ _ _] at hb'
  exact hb'

theorem physical_kac_grand_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    {q : ℕ} (hq : 0 < q) (hu : 2 < (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ) (h : ℝ) :
    Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      (Real.exp (t*h*n)*partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)^
        (gridIndices (m+N) 1).card ≤
      grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h
        (2*((m+N : ℕ)+1)*((q : ℝ)/4)) := by
  have ht0 := lt_trans zero_lt_one ht
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' j, σ j)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hF := grandFinite_fixedInnerBlocks (μ := t*h) ht0.le hβ.le hσ hR hs hsm hq
    (gridIndices (m+N) 1) n
  have hsm' : 2197*t*kernelHeight*(∑' j, prepend a σ j) ≤ (t^2/8)/8 := by
    rw [tsum_prepend a hs]; exact hsmall
  have hG := physical_gibbs_finite ht0.le hβ.le (prepend_nonneg ha hσ)
    (prepend_ge_one hS hR) (summable_prepend a hs) hsm'
    (show volume (cube (2*((m+N : ℕ)+1)*((q : ℝ)/4))) ≠ ⊤ by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (t*h)
  have hb := kac_grandIntegral_lower hC ht hβ.le ha (zero_lt_one.trans_le hS) hσ hR hs hq
    hu.le hN n h hF hG
  rw [grandIntegral_fixedInnerBlocks ht0.le hβ.le hσ hR hs hsm hq] at hb
  exact hb

theorem physical_kac_log_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' j, σ j) ≤ (t^2/8)/8)
    {q : ℕ} (hq : 0 < q) (hu : 2 < (q : ℝ)/4) {N m : ℕ}
    (hN : S+(q : ℝ)/4 ≤ (N : ℝ)*((q : ℝ)/4)) (n : ℕ) (h : ℝ) :
    β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n+
      (gridIndices (m+N) 1).card*(t*h*n+Real.log (partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)) ≤
      Real.log (grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h
        (2*((m+N : ℕ)+1)*((q : ℝ)/4))) := by
  have ht0 := lt_trans zero_lt_one ht
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' j, σ j)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hb' := physical_kac_grand_lower hC ht hβ ha hS hσ hR hs hsmall hq hu (m := m) hN n h
  have hz := partition_pos (measurable_radialPotential (measurable_physicalProfile t hσ hR hs))
    hβ.le (sub_pos.mpr hu) (physicalProfile_stable ht0.le hσ hR hs hsm) n
  have hp : 0 < Real.exp (β*(t*a)*kacLowerGain C S ((q : ℝ)/4) m N n)*
      (Real.exp (t*h*n)*partition (physicalProfile t σ R) β ((q : ℝ)/4-2) n)^
        (gridIndices (m+N) 1).card := mul_pos (Real.exp_pos _) (pow_pos (mul_pos (Real.exp_pos _) hz) _)
  have hl := Real.log_le_log hp hb'
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos (mul_pos (Real.exp_pos _) hz) _).ne',
    Real.log_exp, Real.log_pow, Real.log_mul (Real.exp_pos _).ne' hz.ne', Real.log_exp] at hl
  exact hl

end ContinuumTemperature
end

end OAI
