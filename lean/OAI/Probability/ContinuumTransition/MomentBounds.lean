import OAI.Probability.ContinuumTransition.GeneralGrand

namespace OAI

universe u_1

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem weighted_field_sq {ι : Type u_1} [Fintype ι] (J n : ι → ℝ)
    (hJ : ∀ j, 0 ≤ J j) {M : ℝ} (hrow : ∑ j, J j ≤ M) :
    (∑ j, J j * n j)^2 ≤ M * ∑ j, J j * (n j)^2 := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ)
    Finset.univ (f := J) (g := fun j => J j*(n j)^2)
    (r := fun j => J j*n j) (fun j _ => hJ j)
    (fun j _ => mul_nonneg (hJ j) (sq_nonneg (n j)))
    (fun j _ => by ring_nf; exact le_rfl)
  exact hh.trans (mul_le_mul_of_nonneg_right hrow
    (Finset.sum_nonneg (fun j _ => mul_nonneg (hJ j) (sq_nonneg (n j)))))

theorem cell_insertion_exponent {A M J β B h c n X : ℝ}
    (hA : 0 < A) (hM : M ≤ A/8) (hJ : J ≤ M) (hβ : 0 ≤ β)
    (hc : c = β*A/4) :
    c*n^2+h*n-β*(A-J/2)*n^2+β*B*n+β*n*X ≤
      β*X^2/A+(h+β*B)*n := by
  rw [hc]
  have hsq := sq_nonneg (A*n/2-X)
  have hm := mul_nonneg (show 0 ≤ A/2-J/2 by linarith) (sq_nonneg n)
  have hh := add_nonneg (mul_nonneg (div_nonneg hβ hA.le) hsq) (mul_nonneg hβ hm)
  have he : β*X^2/A+(h+β*B)*n -
      (β*A/4*n^2+h*n-β*(A-J/2)*n^2+β*B*n+β*n*X) =
      β/A*(A*n/2-X)^2+β*((A/2-J/2)*n^2) := by
    field_simp
    ring
  exact sub_nonneg.mp (he ▸ hh)

theorem exp_half_le {C u : ℝ} (hC : 0 < C) :
    Real.exp (u/2) ≤ Real.exp u/(2*C)+C/2 := by
  have he : (Real.exp (u/2))^2 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hh := sq_nonneg (Real.exp (u/2)-C)
  apply (mul_le_mul_iff_left₀ (show 0 < 2*C by positivity)).mp
  calc
    Real.exp (u/2)*(2*C) ≤ Real.exp u+C^2 := by nlinarith only [he, hh]
    _ = (Real.exp u/(2*C)+C/2)*(2*C) := by field_simp

theorem finite_moment_bootstrap {ι : Type u_1} [Fintype ι]
    (F H : ι → ℝ) (θ : ι → ι → ℝ) {C : ℝ} (hC : 0 < C)
    (hF : ∀ i, 0 ≤ F i) (hθ : ∀ i j, 0 ≤ θ i j)
    (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    (hhalf : ∀ i, H i ≤ F i/(2*C)+C/2)
    (hinsert : ∀ i, F i ≤ C*(1+∑ j, θ i j*H j)) :
    ∀ i, F i ≤ 2*C+C^2 := by
  classical
  intro i
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ F ⟨i, Finset.mem_univ i⟩
  have hmax : ∀ j, F j ≤ F k := fun j => hk j (Finset.mem_univ j)
  have hFk := hF k
  have hp : 0 ≤ F k/(2*C)+C/2 := by positivity
  have hsum : ∑ j, θ k j*H j ≤ F k/(2*C)+C/2 := by
    calc
      _ ≤ ∑ j, θ k j*(F k/(2*C)+C/2) := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left ((hhalf j).trans (by gcongr; exact hmax j))
          (hθ k j))
      _ = (∑ j, θ k j)*(F k/(2*C)+C/2) := by rw [Finset.sum_mul]
      _ ≤ 1*(F k/(2*C)+C/2) := mul_le_mul_of_nonneg_right (hrow k) hp
      _ = F k/(2*C)+C/2 := one_mul _
  have hb := (hinsert k).trans (mul_le_mul_of_nonneg_left (show 1+∑ j, θ k j*H j ≤ 1+(F k/(2*C)+C/2) by linarith only [hsum]) hC.le)
  have he : C*(1+(F k/(2*C)+C/2)) = C+F k/2+C^2/2 := by field_simp; ring
  rw [he] at hb
  exact (hmax i).trans (by nlinarith only [hb])

end ContinuumTemperature
end

end OAI
