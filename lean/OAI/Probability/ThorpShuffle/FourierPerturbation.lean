import OAI.Probability.ThorpShuffle.Trimming

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp

namespace Fourier
open scoped Classical
variable {G : Type} [Fintype G] [Group G]

omit [Group G] in
lemma tv_nonneg (μ ν : G → ℝ) : 0 ≤ tv μ ν := by unfold tv; positivity

omit [Group G] in
lemma tv_triangle (μ ν η : G → ℝ) : tv μ η ≤ tv μ ν + tv ν η := by
  unfold tv
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun g _ => by simpa only [sub_add_sub_cancel] using abs_add_le (μ g-ν g) (ν g-η g))

lemma tv_realConv_left (μ ν η : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (h1 : ∑ g, μ g = 1) :
    tv (realConv μ ν) (realConv μ η) ≤ tv ν η := by
  have hb : (∑ z, |realConv μ ν z - realConv μ η z|) ≤ ∑ z, |ν z-η z| := by
    calc
      _ = ∑ z, |∑ g, μ g * (ν (g⁻¹*z)-η (g⁻¹*z))| := by
        simp only [realConv, mul_sub, Finset.sum_sub_distrib]
      _ ≤ ∑ z, ∑ g, μ g * |ν (g⁻¹*z)-η (g⁻¹*z)| := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [abs_mul, abs_of_nonneg (hμ _)] using
          Finset.abs_sum_le_sum_abs (fun g => μ g * (ν (g⁻¹*z)-η (g⁻¹*z))) Finset.univ
      _ = (∑ g, μ g) * ∑ z, |ν z-η z| := by
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun z => |ν z-η z|)
      _ = _ := by rw [h1, one_mul]
  exact mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)

lemma tv_realConv_right (μ ν η : G → ℝ) (hη : ∀ g, 0 ≤ η g) (h1 : ∑ g, η g = 1) :
    tv (realConv μ η) (realConv ν η) ≤ tv μ ν := by
  have hb : (∑ z, |realConv μ η z - realConv ν η z|) ≤ ∑ z, |μ z-ν z| := by
    calc
      _ = ∑ z, |∑ g, (μ g-ν g) * η (g⁻¹*z)| := by
        simp only [realConv, sub_mul, Finset.sum_sub_distrib]
      _ ≤ ∑ z, ∑ g, |μ g-ν g| * η (g⁻¹*z) := by
        apply Finset.sum_le_sum
        intro z _
        simpa only [abs_mul, abs_of_nonneg (hη _)] using
          Finset.abs_sum_le_sum_abs (fun g => (μ g-ν g) * η (g⁻¹*z)) Finset.univ
      _ = (∑ g, |μ g-ν g|) * ∑ z, η z := by
        rw [Finset.sum_comm, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) η
      _ = _ := by rw [h1, mul_one]
  exact mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)

lemma tv_realConv (μ ν μ' ν' : G → ℝ) (hμ' : ∀ g, 0 ≤ μ' g) (hμ1 : ∑ g, μ' g = 1)
    (hν : ∀ g, 0 ≤ ν g) (hν1 : ∑ g, ν g = 1) :
    tv (realConv μ ν) (realConv μ' ν') ≤ tv μ μ' + tv ν ν' := by
  exact (tv_triangle _ (realConv μ' ν) _).trans
    (add_le_add (tv_realConv_right μ μ' ν hν hν1) (tv_realConv_left μ' ν ν' hμ' hμ1))

lemma tv_realPower (μ ν : G → ℝ) (hμ : ∀ g, 0 ≤ μ g) (hμ1 : ∑ g, μ g = 1)
    (hν : ∀ g, 0 ≤ ν g) (hν1 : ∑ g, ν g = 1) (k : ℕ) :
    tv (realPower μ k) (realPower ν k) ≤ (k : ℝ) * tv μ ν := by
  induction k with
  | zero => simp [realPower, tv]
  | succ k ih =>
      calc
        _ ≤ tv μ ν + tv (realPower μ k) (realPower ν k) :=
          tv_realConv μ (realPower μ k) ν (realPower ν k) hν hν1 (realPower_nonneg μ hμ k) (realPower_sum μ hμ1 k)
        _ ≤ tv μ ν + (k : ℝ) * tv μ ν := add_le_add_right ih _
        _ = _ := by push_cast; ring

end Fourier

end Thorp

end

end OAI
