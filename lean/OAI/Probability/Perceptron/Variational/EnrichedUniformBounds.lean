import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedDiagonalField

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma diagonalMark_norm_le {I : Type} [Fintype I] (c : I → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) : ‖diagonalMark c‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hs : ‖diagonalMark c x‖^2 ≤ (C*‖x‖)^2 := by
    rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simp only [Real.norm_eq_abs,sq_abs,diagonalMark_apply,mul_pow]
    exact mul_le_mul_of_nonneg_right (by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (c i)) (hc i) 2) (sq_nonneg (x i))
  nlinarith [norm_nonneg (diagonalMark c x),mul_nonneg hC (norm_nonneg x)]

lemma enrichedRootMap_norm_le {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (hh : h 0 ≤ H) :
    ‖enrichedRootMap p d h‖ ≤ Real.sqrt (2*H+1) := by
  apply diagonalMark_norm_le _ (Real.sqrt_nonneg _)
  intro i
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  cases i with
  | inl i => dsimp [enrichedCoordinateLevel]; linarith
  | inr i =>
    simp only [enrichedCoordinateLevel,Fin.val_zero,Nat.cast_zero,zero_div]
    by_cases hd : d i.1=0
    · rw [hd,pow_zero]; linarith
    · rw [zero_pow hd]; positivity

lemma perturbationScale_le_one (N : ℕ) (hN : 1 ≤ N) : perturbationScale N ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)

lemma perturbationWeight_eq (j : ℕ) : (2:ℝ)^(-((j+1:ℕ):ℤ))=(1/2:ℝ)^(j+1) := by
  simp only [zpow_neg,zpow_natCast,one_div,inv_pow]

lemma half_power_sum_le_one (N : ℕ) : (∑ j : Fin N, (1/2:ℝ)^(j.val+1)) ≤ 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (1/2:ℝ)^(j+1)) N]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  nlinarith [sum_geometric_two_le N]

lemma perturbationAmplitude_square_le (N : ℕ) (hN : 1 ≤ N) (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Icc 1 2) (j : Fin N) :
    perturbationAmplitude N u j^2 ≤ 4*(N:ℝ)*(1/2:ℝ)^(j.val+1) := by
  let w : ℝ := (1/2:ℝ)^(j.val+1)
  have hw0 : 0 ≤ w := pow_nonneg (by norm_num) _
  have hw1 : w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he0 : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have he1 := perturbationScale_le_one N hN
  have he2 : perturbationScale N^2 ≤ 1 := by nlinarith
  have hu2 : (u j)^2 ≤ 4 := by have h1 := (hu j).1; have h2 := (hu j).2; nlinarith
  have hw2 : w^2 ≤ w := by nlinarith
  unfold perturbationAmplitude
  rw [perturbationWeight_eq]
  change (Real.sqrt (N:ℝ)*perturbationScale N*w*u j)^2 ≤ _
  simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  calc
    _ ≤ (N:ℝ)*1*w^2*4 := by
      apply mul_le_mul _ hu2 (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 (Nat.cast_nonneg N)) (sq_nonneg w)
    _ ≤ 4*(N:ℝ)*w := by nlinarith [mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (N:ℝ) by positivity)]

lemma enrichedFeatureBound_sq_le (N : ℕ) (hN : 1 ≤ N) (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Icc 1 2) : (enrichedFeatureBound N u:ℝ)^2 ≤ 5*(N:ℝ) := by
  change (Real.sqrt ((N:ℝ)+∑ j, perturbationAmplitude N u j^2))^2 ≤ _
  rw [Real.sq_sqrt (by positivity)]
  have hs : (∑ j : Fin N, perturbationAmplitude N u j^2) ≤ 4*(N:ℝ) := by
    calc
      _ ≤ ∑ j : Fin N, 4*(N:ℝ)*(1/2:ℝ)^(j.val+1) :=
        Finset.sum_le_sum fun j _ => perturbationAmplitude_square_le N hN u hu j
      _ = 4*(N:ℝ)*(∑ j : Fin N, (1/2:ℝ)^(j.val+1)) := (Finset.mul_sum _ _ _).symm
      _ ≤ 4*(N:ℝ)*1 := mul_le_mul_of_nonneg_left (half_power_sum_le_one N) (by positivity)
      _ = _ := mul_one _
  linarith

lemma finite_profile_telescope {k : ℕ} (q : Fin (k+1) → ℝ) :
    q 0 + ∑ i : Fin k, (q i.succ-q i.castSucc) = q (Fin.last k) := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

def profileGaussianRoot {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) (i : I) : ℝ :=
  Real.sqrt (q 0 i)

def profileGaussianStep {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (j : ℕ) (i : I) : ℝ :=
  if hj : j<k then Real.sqrt (q ⟨k-j,by omega⟩ i-q ⟨k-j-1,by omega⟩ i) else 0

lemma profileGaussian_coefficient {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ) :
    hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) =
      Fin.cases (fun i => Real.sqrt (q 0 i))
        (fun l i => Real.sqrt (q l.succ i-q l.castSucc i)) := by
  funext l i
  induction l using Fin.cases with
  | zero => rfl
  | succ l =>
    simp only [hierarchyRowCoefficients,Fin.cases_succ,profileGaussianStep,
      dite_eq_left (show k-1-l.val<k by omega)]
    congr 2 <;> congr 1 <;> apply Fin.ext <;> simp only [Fin.val_succ,Fin.val_castSucc] <;> omega

lemma profileGaussian_coefficient_squares {I : Type} {k : ℕ} (q : Fin (k+1) → I → ℝ)
    (h0 : ∀ i, 0 ≤ q 0 i) (hq : ∀ i, Monotone (fun l => q l i)) (i : I) :
    (∑ l : Fin (k+1), hierarchyRowCoefficients k (profileGaussianRoot q) (profileGaussianStep q) l i^2) =
      q (Fin.last k) i := by
  rw [profileGaussian_coefficient,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.sq_sqrt (h0 i)]
  have he (j : Fin k) : (Real.sqrt (q j.succ i-q j.castSucc i))^2 = q j.succ i-q j.castSucc i :=
    Real.sq_sqrt (sub_nonneg.mpr (hq i (by simp [Fin.le_iff_val_le_val])))
  simp_rw [he]
  exact finite_profile_telescope (fun l => q l i)

lemma enrichedCoordinateLevel_nonneg {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} (hh : ∀ l, 0 ≤ h l) (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    0 ≤ enrichedCoordinateLevel p d h l i := by
  cases i with
  | inl i => exact mul_nonneg (by norm_num) (hh l)
  | inr i => exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma enrichedCoordinateLevel_monotone {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} (hh : Monotone h) (i : EnrichedIndex N N p) :
    Monotone (fun l => enrichedCoordinateLevel p d h l i) := by
  intro a b hab
  cases i with
  | inl i => exact mul_le_mul_of_nonneg_left (hh hab) (by norm_num)
  | inr i =>
    apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg _)

lemma enrichedCoordinateLevel_le {N k : ℕ} (p d : Fin N → ℕ)
    {h : Fin (k+1) → ℝ} {H : ℝ} (hH : 0 ≤ H) (hh : ∀ l, h l ≤ H)
    (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    enrichedCoordinateLevel p d h l i ≤ 2*H+1 := by
  cases i with
  | inl i => dsimp [enrichedCoordinateLevel]; linarith [hh l]
  | inr i =>
    have ht : ((l.val:ℝ)/(k+1:ℕ)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast l.isLt.le
    have ht0 : 0 ≤ ((l.val:ℝ)/(k+1:ℕ)) := by positivity
    exact (pow_le_one₀ ht0 ht).trans (by linarith)

lemma enrichedIncrementMap_profile {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (j : ℕ) :
    enrichedIncrementMap p d h j = diagonalMark (profileGaussianStep (enrichedCoordinateLevel p d h) j) := by
  by_cases hj : j<k
  · rw [enrichedIncrementMap,dite_eq_left hj]
    congr 1
    funext i
    simp only [profileGaussianStep,dite_eq_left hj]
  · apply ContinuousLinearMap.ext
    intro x
    ext i
    simp [enrichedIncrementMap,profileGaussianStep,hj,diagonalMark_apply]

def sourceGaussianRow {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ) (u : Fin N → ℝ) :
    ℕ → NormalizedSpin N × IndexedLeaf k → ℝ :=
  indexedGaussianRow k (hierarchyRowCoefficients k
    (profileGaussianRoot (enrichedCoordinateLevel p d h))
    (profileGaussianStep (enrichedCoordinateLevel p d h))) (sourceEnrichedFeature N p u)

lemma sourceGaussianRow_measurable {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (i : ℕ) : Measurable (sourceGaussianRow p d h u i) :=
  indexedGaussianRow_measurable _ _ (enrichedFeature_continuous _ _ _ _ _).measurable i

lemma sourceGaussianRow_square_bound {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) {H : ℝ}
    (hH : 0 ≤ H) (hhH : ∀ l, h l ≤ H) (x : NormalizedSpin N × IndexedLeaf k) :
    (∑ i : Fin (indexedGaussianRowLength (I := EnrichedIndex N N p) k x),
      sourceGaussianRow p d h u i.val x^2) ≤ (2*H+1)*(enrichedFeatureBound N u:ℝ)^2 := by
  apply indexedGaussianRow_norm_le
  · intro i
    rw [profileGaussian_coefficient_squares _ (enrichedCoordinateLevel_nonneg p d hh0 0)
      (enrichedCoordinateLevel_monotone p d hh)]
    exact enrichedCoordinateLevel_le p d hH hhH _ i
  · positivity
  · intro y
    have he := congrArg (fun t : ℝ => t^2) (sourceEnrichedFeature_norm N p u y)
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le

lemma sourceGaussianRow_identity {N k : ℕ} (p d : Fin N → ℕ) (h : Fin (k+1) → ℝ)
    (u : Fin N → ℝ) (g : ℕ → ℝ) (x : NormalizedSpin N × IndexedLeaf k) :
    countableGaussianField (sourceGaussianRow p d h u)
      (indexedGaussianRowLength (I := EnrichedIndex N N p) k) g x =
      inner ℝ (sourceEnrichedFeature N p u x.1)
        (indexedLeafState (gaussianLinearMarkStep (enrichedIncrementMap p d h)) k
          ((fun _ => enrichedRootMap p d h (indexedGaussianDisorder k (EnrichedIndex N N p) g).1),
            (indexedGaussianDisorder k (EnrichedIndex N N p) g).2) x.2 0) := by
  unfold sourceGaussianRow
  rw [indexedGaussianRow_diagonal_identity]
  have he : enrichedIncrementMap p d h = fun j => diagonalMark
      (profileGaussianStep (enrichedCoordinateLevel p d h) j) :=
    funext (enrichedIncrementMap_profile p d h)
  rw [he]
  rfl

end SphericalPerceptronFreeEnergy

end

end OAI
