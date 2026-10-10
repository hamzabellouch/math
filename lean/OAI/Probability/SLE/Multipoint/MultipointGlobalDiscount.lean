import OAI.Probability.SLE.Multipoint.MultipointUniformCost
import OAI.Probability.SLE.Multipoint.MultipointIntegratedCost

namespace OAI

/-! A uniform discount budget from the individual live intervals. The
pair sum is ordered, as in the product generator. -/

noncomputable section
open Set Filter MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def singleDriftConstant (κ : ℝ) : ℝ :=
  driftAllowance (greenExponent κ)*driftThreshold (greenExponent κ)^(-greenExponent κ)

lemma singleDriftConstant_pos {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    0 < singleDriftConstant κ := by
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  exact mul_pos (driftAllowance_pos hp) (Real.rpow_pos_of_pos (driftThreshold_pos hp) _)

def uniformDiscountBudget {ι : Type*} [DecidableEq ι] (κ β : ℝ) (I : Finset ι) : ℝ :=
  κ*(singleDriftConstant κ*((I.card : ℝ)*(2/(κ*β))) +
    allPatternYoungConstant κ I*((I.offDiag.card : ℝ)*
      interactionBudget 2 (exponent (greenExponent κ)*(κ*β))))

lemma productDriftCost_le_active_envelope {ι : Type*} [DecidableEq ι]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {I s : Finset ι} (hs : s ⊆ I)
    (D σ : ι → ℝ) (hD : ∀ i ∈ s, 0 < D i) (z : ι → ℂ × ℝ) (x t : ℝ)
    (a b : ι → ℝ) (c d : ι × ι → ℝ) (f : ι → ℝ → ℝ) (g : ι × ι → ℝ → ℝ)
    (hf0 : ∀ i ∈ I, 0 ≤ f i t) (hg0 : ∀ ij ∈ I.offDiag, 0 ≤ g ij t)
    (hfi : ∀ i ∈ s, t ∈ Ioc (a i) (b i))
    (hgi : ∀ ij ∈ s.offDiag, t ∈ Ioc (c ij) (d ij))
    (hf : ∀ i ∈ s, branchRegulator κ (D i) (σ i) (z i)*logVelocity κ (z i) x^2 = f i t)
    (hg : ∀ ij ∈ s.offDiag,
      (branchRegulator κ (D ij.1) (σ ij.1) (z ij.1)*
        branchRegulator κ (D ij.2) (σ ij.2) (z ij.2))^(-exponent (greenExponent κ))*
        (logVelocity κ (z ij.1) x*logVelocity κ (z ij.2) x) = g ij t) :
    productDriftCost s κ D σ z x ≤
      κ*(singleDriftConstant κ*(∑ i ∈ I, (Ioc (a i) (b i)).indicator (f i) t) +
        allPatternYoungConstant κ I*(∑ ij ∈ I.offDiag, (Ioc (c ij) (d ij)).indicator (g ij) t)) := by
  apply (productDriftCost_le_uniform hκ hκ8 hs D σ hD z x).trans
  apply mul_le_mul_of_nonneg_left _ hκ.le
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (singleDriftConstant_pos hκ hκ8).le
    calc
      _ = ∑ i ∈ s, (Ioc (a i) (b i)).indicator (f i) t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hf i hi, indicator_of_mem (hfi i hi)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun i hi _ => by
        by_cases ht : t ∈ Ioc (a i) (b i)
        · simpa only [indicator_of_mem ht] using hf0 i hi
        · simp only [indicator_of_notMem ht, le_refl])
  · apply mul_le_mul_of_nonneg_left _ (allPatternYoungConstant_pos hκ hκ8 I).le
    calc
      _ = ∑ ij ∈ s.offDiag, (Ioc (c ij) (d ij)).indicator (g ij) t := by
        apply Finset.sum_congr rfl
        intro ij hij
        rw [hg ij hij, indicator_of_mem (hgi ij hij)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.offDiag_mono hs) (fun ij hij _ => by
        by_cases ht : t ∈ Ioc (c ij) (d ij)
        · simpa only [indicator_of_mem ht] using hg0 ij hij
        · simp only [indicator_of_notMem ht, le_refl])

theorem integrated_uniform_discount_le {ι : Type*} [DecidableEq ι]
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (β : ℝ) (I : Finset ι)
    (a b : ι → ℝ) (c d : ι × ι → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (f : ι → ℝ → ℝ) (g : ι × ι → ℝ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hab : ∀ i ∈ I, a i ≤ b i) (hb : ∀ i ∈ I, b i ≤ H)
    (hc : ∀ ij ∈ I.offDiag, 0 ≤ c ij) (hcd : ∀ ij ∈ I.offDiag, c ij ≤ d ij)
    (hd : ∀ ij ∈ I.offDiag, d ij ≤ H)
    (hf : ∀ i ∈ I, IntervalIntegrable (f i) volume (a i) (b i))
    (hg : ∀ ij ∈ I.offDiag, IntervalIntegrable (g ij) volume (c ij) (d ij))
    (hfB : ∀ i ∈ I, (∫ t in a i..b i, f i t) ≤ 2/(κ*β))
    (hgB : ∀ ij ∈ I.offDiag, (∫ t in c ij..d ij, g ij t) ≤
      interactionBudget 2 (exponent (greenExponent κ)*(κ*β)))
    (R : ℝ → ℝ) (hR : IntervalIntegrable R volume 0 H)
    (hle : R ≤ᵐ[volume.restrict (Icc 0 H)] (fun t =>
      κ*(singleDriftConstant κ*(∑ i ∈ I, (Ioc (a i) (b i)).indicator (f i) t) +
        allPatternYoungConstant κ I*(∑ ij ∈ I.offDiag, (Ioc (c ij) (d ij)).indicator (g ij) t)))) :
    (∫ t in 0..H, R t) ≤ uniformDiscountBudget κ β I := by
  let F := fun t => ∑ i ∈ I, (Ioc (a i) (b i)).indicator (f i) t
  let G := fun t => ∑ ij ∈ I.offDiag, (Ioc (c ij) (d ij)).indicator (g ij) t
  have hFi : IntervalIntegrable F volume 0 H := by
    convert (IntervalIntegrable.sum (a := 0) (b := H) I
      (fun i hi => active_interval_integrable (f i) (hf i hi))) using 1
    ext t
    simp only [F, Finset.sum_apply]
  have hGi : IntervalIntegrable G volume 0 H := by
    convert (IntervalIntegrable.sum (a := 0) (b := H) I.offDiag
      (fun i hi => active_interval_integrable (g i) (hg i hi))) using 1
    ext t
    simp only [G, Finset.sum_apply]
  have hFB : (∫ t in 0..H, F t) ≤ (I.card : ℝ)*(2/(κ*β)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      finite_active_cost_integral_le I a b (fun _ => 2/(κ*β)) f H ha hab hb hf hfB
  have hGB : (∫ t in 0..H, G t) ≤ (I.offDiag.card : ℝ)*
      interactionBudget 2 (exponent (greenExponent κ)*(κ*β)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      finite_active_cost_integral_le I.offDiag c d
        (fun _ => interactionBudget 2 (exponent (greenExponent κ)*(κ*β))) g H hc hcd hd hg hgB
  apply (intervalIntegral.integral_mono_ae_restrict hH hR
    (((hFi.const_mul _).add (hGi.const_mul _)).const_mul _) hle).trans
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hFi.const_mul _) (hGi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hκ.le
  exact add_le_add
    (mul_le_mul_of_nonneg_left hFB (singleDriftConstant_pos hκ hκ8).le)
    (mul_le_mul_of_nonneg_left hGB (allPatternYoungConstant_pos hκ hκ8 I).le)

end SLEExactGauge.Multipoint

end

end OAI
