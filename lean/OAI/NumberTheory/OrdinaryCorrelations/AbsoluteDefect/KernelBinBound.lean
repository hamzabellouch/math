import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Phase

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory

namespace OrdinaryDirichletMeanSquare

lemma kernel_bin_bound {u v : ℝ} {j k : ℕ}
    (hu : |u-j| ≤ 1) (hv : |v-k| ≤ 1) :
    Real.exp (-(u-v)^2/4) ≤
      Real.exp 3 * Real.exp (-(Nat.dist j k : ℝ)) := by
  have hd : |(j:ℝ)-k| ≤ |u-v|+2 := by
    have h := abs_add_three ((j:ℝ)-u) (u-v) (v-k)
    have hj : |(j:ℝ)-u| ≤ 1 := by simpa [abs_sub_comm] using hu
    have he : (j:ℝ)-u+(u-v)+(v-k) = (j:ℝ)-k := by ring
    rw [he] at h
    linarith
  rw [←Real.exp_add,Real.exp_le_exp,dist_real]
  nlinarith [sq_nonneg (|u-v|-2),sq_abs (u-v)]

lemma sum_group_bins {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (b : ι → ℕ) (a : ι → ℝ) (F : ℕ → ℝ) :
    ∑ n ∈ s, a n * F (b n) =
      ∑ j ∈ s.image b, (∑ n ∈ s.filter (fun n => b n=j), a n) * F j := by
  classical
  simp_rw [Finset.sum_mul]
  have he := Finset.sum_fiberwise_of_maps_to (s:=s) (t:=s.image b) (g:=b)
    (fun n hn => Finset.mem_image.mpr ⟨n,hn,rfl⟩) (fun n => a n*F (b n))
  rw [←he]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

lemma pair_group_bins {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (b : ι → ℕ) (a : ι → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ m ∈ s, ∑ n ∈ s, a m*a n*K (b m) (b n)) =
      ∑ j ∈ s.image b, ∑ k ∈ s.image b,
        (∑ m ∈ s.filter (fun m => b m=j), a m) *
        (∑ n ∈ s.filter (fun n => b n=k), a n) * K j k := by
  classical
  simp_rw [mul_assoc,←Finset.mul_sum]
  rw [sum_group_bins s b a (fun j => ∑ n ∈ s, a n*K j (b n))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sum_group_bins s b a (K j),Finset.mul_sum]

theorem binned_gaussian_energy {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) (b : ι → ℕ)
    (hb : ∀ n ∈ s, |u n-b n| ≤ 1) :
    (∫ x : ℝ, gaussian x * ‖polynomial s a u x‖^2) ≤
      gaussianConstant * Real.exp 3 * 4 *
        ∑ j ∈ s.image b, (∑ n ∈ s.filter (fun n => b n=j), ‖a n‖)^2 := by
  classical
  apply (gaussian_polynomial_energy s a u).trans
  have hC : 0 ≤ gaussianConstant := norm_nonneg _
  calc
    _ ≤ gaussianConstant * ∑ m ∈ s, ∑ n ∈ s,
        ‖a m‖*‖a n‖*(Real.exp 3*Real.exp (-(Nat.dist (b m) (b n):ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (kernel_bin_bound (hb m hm) (hb n hn)) (by positivity)
    _ = gaussianConstant * Real.exp 3 *
        (∑ j ∈ s.image b, ∑ k ∈ s.image b,
          (∑ m ∈ s.filter (fun m => b m=j), ‖a m‖) *
          (∑ n ∈ s.filter (fun n => b n=k), ‖a n‖) *
          Real.exp (-(Nat.dist j k:ℝ))) := by
      rw [←pair_group_bins s b (fun n => ‖a n‖)]
      simp_rw [show ∀ m n : ι, ‖a m‖*‖a n‖*(Real.exp 3*
        Real.exp (-(Nat.dist (b m) (b n):ℝ))) = Real.exp 3 *
        (‖a m‖*‖a n‖*Real.exp (-(Nat.dist (b m) (b n):ℝ))) by intros; ring,
        ←Finset.mul_sum]
      ring
    _ ≤ _ := by
      have h := finite_schur (s.image b)
        (fun j => ∑ n ∈ s.filter (fun n => b n=j), ‖a n‖)
        (fun j k => Real.exp (-(Nat.dist j k:ℝ))) 4
        (fun _ _ _ _ => (Real.exp_pos _).le)
        (fun j _ k _ => by rw [Nat.dist_comm])
        (fun j _ => by simpa only [neg_mul,one_mul,div_one,show (2:ℝ)+2=4 by norm_num] using (geometric_exponential_row (s.image b) j (show (0:ℝ)<1 by norm_num)))
      have hm := mul_le_mul_of_nonneg_left h (mul_nonneg hC (Real.exp_pos 3).le)
      simpa [mul_assoc] using hm

end OrdinaryDirichletMeanSquare

end

end OAI
