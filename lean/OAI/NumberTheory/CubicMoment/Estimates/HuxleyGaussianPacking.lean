import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGridPacking

namespace OAI

/-! Gaussian mass of the separated lifted fractions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma huxley_gaussian_weight_summable :
    Summable (fun k : ℕ => ((k:ℝ)+2)*Real.exp (-(k:ℝ))) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (show (0:ℝ) < 1 by norm_num)
  have h0 := Real.summable_exp_neg_nat
  have h := h1.add (h0.mul_left 2)
  simpa only [pow_one,one_mul,add_mul,neg_one_mul] using h

def huxleyGaussianConstant : ℝ :=
  6000*∑' k : ℕ, ((k:ℝ)+2)*Real.exp (-(k:ℝ))

lemma huxleyGaussianConstant_pos : 0 < huxleyGaussianConstant := by
  unfold huxleyGaussianConstant
  apply mul_pos (by norm_num)
  have h := huxley_gaussian_weight_summable.le_tsum 0 (fun _ _ => by positivity)
  norm_num at h
  linarith

lemma huxleyLift_gaussian_bin_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q) (k : ℕ) :
    (∑ i ∈ S with ⌊t*‖i.frequency-z‖^2⌋₊ = k,
      Real.exp (-t*‖i.frequency-z‖^2)) ≤
      6000*(1+Q^2*((k:ℝ)+1)/t)*Real.exp (-(k:ℝ)) := by
  let U := S.filter (fun i => ⌊t*‖i.frequency-z‖^2⌋₊ = k)
  let R := Real.sqrt (((k:ℝ)+1)/t)
  have hnum : 0 ≤ ((k:ℝ)+1)/t := by positivity
  have hR : R^2 = ((k:ℝ)+1)/t := Real.sq_sqrt hnum
  have hball : ∀ i ∈ U, ‖i.frequency-z‖ ≤ R := by
    intro i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hlt := Nat.lt_floor_add_one (t*‖i.frequency-z‖^2)
    rw [hk] at hlt
    apply (Real.le_sqrt (_root_.norm_nonneg _) hnum).mpr
    exact (le_div_iff₀ ht).mpr (by nlinarith)
  have hcard := huxleyLift_disk_count Q hQ z R (Real.sqrt_nonneg _) U
    (fun i hi => hred i (Finset.mem_filter.mp hi).1) hball
  have hpoint : ∀ i ∈ U, Real.exp (-t*‖i.frequency-z‖^2) ≤ Real.exp (-(k:ℝ)) := by
    intro i hi
    have hk := (Finset.mem_filter.mp hi).2
    have hlo := Nat.floor_le (show 0 ≤ t*‖i.frequency-z‖^2 by positivity)
    rw [hk] at hlo
    exact Real.exp_le_exp.mpr (by nlinarith)
  change (∑ i ∈ U, Real.exp (-t*‖i.frequency-z‖^2)) ≤ _
  calc
    _ ≤ ∑ i ∈ U, Real.exp (-(k:ℝ)) := Finset.sum_le_sum hpoint
    _ = (U.card:ℝ)*Real.exp (-(k:ℝ)) := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      rw [hR] at hcard
      simpa only [mul_div_assoc] using hcard

/-- The Gaussian row bound has exactly the required two-dimensional scale. -/
lemma huxleyLift_gaussian_sum_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q) :
    (∑ i ∈ S, Real.exp (-t*‖i.frequency-z‖^2)) ≤
      huxleyGaussianConstant*(1+Q^2/t) := by
  let bin := fun i : HuxleyLift => ⌊t*‖i.frequency-z‖^2⌋₊
  let K := S.image bin
  have he : (∑ i ∈ S, Real.exp (-t*‖i.frequency-z‖^2)) =
      ∑ k ∈ K, ∑ i ∈ S with bin i = k, Real.exp (-t*‖i.frequency-z‖^2) := by
    exact (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) _).symm
  have hα : 0 ≤ Q^2/t := by positivity
  calc
    _ = _ := he
    _ ≤ ∑ k ∈ K, 6000*(1+Q^2*((k:ℝ)+1)/t)*Real.exp (-(k:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact huxleyLift_gaussian_bin_bound Q hQ z ht S hred k
    _ ≤ ∑ k ∈ K, (6000*(1+Q^2/t))*(((k:ℝ)+2)*Real.exp (-(k:ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hpoly : 1+Q^2*((k:ℝ)+1)/t ≤ (1+Q^2/t)*((k:ℝ)+2) := by
        have hkn : (0:ℝ) ≤ k := Nat.cast_nonneg k
        rw [show Q^2*((k:ℝ)+1)/t = (Q^2/t)*((k:ℝ)+1) by ring]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-(k:ℝ))).le]
    _ = (6000*(1+Q^2/t))*∑ k ∈ K, ((k:ℝ)+2)*Real.exp (-(k:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (6000*(1+Q^2/t))*∑' k : ℕ, ((k:ℝ)+2)*Real.exp (-(k:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact huxley_gaussian_weight_summable.sum_le_tsum K (fun k hk => by positivity)
    _ = _ := by unfold huxleyGaussianConstant; ring

def huxleyLiftGaussian (Q t : ℝ) (z : ℂ) (i : HuxleyLift) : ℝ :=
  if i.reduced Q then Real.exp (-t*‖i.frequency-z‖^2) else 0

lemma huxleyLiftGaussian_finite_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) (S : Finset HuxleyLift) :
    (∑ i ∈ S, huxleyLiftGaussian Q t z i) ≤ huxleyGaussianConstant*(1+Q^2/t) := by
  simp only [huxleyLiftGaussian,← Finset.sum_filter]
  exact huxleyLift_gaussian_sum_bound Q hQ z ht (S.filter (fun i => i.reduced Q))
    (fun i hi => (Finset.mem_filter.mp hi).2)

lemma huxleyLiftGaussian_summable (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) : Summable (huxleyLiftGaussian Q t z) := by
  apply summable_of_sum_le (c := huxleyGaussianConstant*(1+Q^2/t))
  · intro i
    unfold huxleyLiftGaussian
    split_ifs <;> positivity
  · exact huxleyLiftGaussian_finite_bound Q hQ z ht

lemma huxleyLiftGaussian_tsum_bound (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    {t : ℝ} (ht : 0 < t) :
    (∑' i : HuxleyLift, huxleyLiftGaussian Q t z i) ≤
      huxleyGaussianConstant*(1+Q^2/t) := by
  apply Real.tsum_le_of_sum_le
  · intro i
    unfold huxleyLiftGaussian
    split_ifs <;> positivity
  · exact huxleyLiftGaussian_finite_bound Q hQ z ht

end CubicFirstMoment

end

end OAI
