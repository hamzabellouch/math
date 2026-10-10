import OAI.Probability.ContinuumTransition.LowerRows

namespace OAI

universe u_1 u_2

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem double_sum_comp_eq {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (J : κ → κ → ℝ) :
    (∑ i, ∑ j, J (c i) (c j)) = ∑ k, ∑ l,
      J k l*(Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ) := by
  calc
    _ = ∑ i, ∑ l, (Fintype.card {j // c j = l} : ℝ)*J (c i) l := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_comp_eq_sum_fibres c (fun l => J (c i) l)
    _ = ∑ k, (Fintype.card {i // c i = k} : ℝ)*
        (∑ l, (Fintype.card {j // c j = l} : ℝ)*J k l) :=
      sum_comp_eq_sum_fibres c (fun k => ∑ l, (Fintype.card {j // c j = l} : ℝ)*J k l)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem gibbsEnergy_eq_sum_sub_diag (V : Space → Space → ℝ)
    {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy V x = ((∑ i, ∑ j, V (x i) (x j))-(∑ i, V (x i) (x i)))/2 := by
  have he (i j : ι) : (if i = j then 0 else V (x i) (x j)) =
      V (x i) (x j)-(if i = j then V (x i) (x j) else 0) := by
    split_ifs <;> ring
  simp only [gibbsEnergy, he, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem kac_energy_upper {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) {ι : Type} [Fintype ι]
    (s : Finset Lattice) (c : ι → s) (x : ι → Space)
    (hx : ∀ i, x i ∈ gridBox u (c i)) :
    gibbsEnergy (fun x y => scaledKernel R (x-y)) x ≤
      (1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3)/(2*u^3)*
        ∑ k : s, (Fintype.card {i // c i = k} : ℝ)^2 := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let J : s → s → ℝ := fun k l => kacUpper C R u (gridCenter u k) (gridCenter u l)
  have hJ : ∀ k l, 0 ≤ J k l := fun _ _ => kacUpper_nonneg C.coe_nonneg hR hu.le _ _
  have hsym (x y : Space) : scaledKernel R (x-y) = scaledKernel R (y-x) := by
    rw [← neg_sub x y, scaledKernel_neg]
  have hp := pairSum_le_cell_quadratic c J (fun i j => scaledKernel R (x i-x j)) hJ
    (fun i j => hsym _ _) (fun i j => (kac_pair_bounds hC hR
      (gridBox_center_distance hu (hx i)) (gridBox_center_distance hu (hx j))).2)
  rw [← gibbsEnergy_eq_pairSum _ hsym x] at hp
  have hr (k : s) : (∑ l : s, J k l) ≤
      (1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3)/u^3 := by
    apply (le_div_iff₀ (pow_pos hu 3)).2
    have hh := kacUpper_row hC hR hu (gridCenter u k) s
    change (∑ l : s, kacUpper C R u (gridCenter u k) (gridCenter u l))*u^3 ≤ _
    rw [Finset.sum_coe_sort s (fun l : Lattice => kacUpper C R u (gridCenter u k) (gridCenter u l))]
    simpa only [mul_comm] using hh
  have hq := row_sum_quadratic_bound J
    (fun k : s => (Fintype.card {i // c i = k} : ℝ))
    ((1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3)/u^3) hJ
    (fun k l => kacUpper_symm C R u _ _) hr
  calc
    _ ≤ (1/2 : ℝ)*∑ k : s, ∑ l : s,
      J k l*(Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ) := hp
    _ ≤ (1/2 : ℝ)*(((1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3)/u^3)*
        ∑ k : s, (Fintype.card {i // c i = k} : ℝ)^2) := mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = _ := by ring

theorem kac_energy_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (c : ι → κ) (centers : κ → Space) (x : ι → Space)
    (hx : ∀ i, ‖x i-centers (c i)‖ ≤ 2*u) :
    ((∑ k, ∑ l, kacLower C R u (centers k) (centers l)*
      (Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ))-
      (Fintype.card ι : ℝ)*scaledKernel R 0)/2 ≤
        gibbsEnergy (fun x y => scaledKernel R (x-y)) x := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      (kac_pair_bounds hC hR (hx i) (hx j)).1))
  rw [double_sum_comp_eq c (fun k l => kacLower C R u (centers k) (centers l))] at hh
  rw [gibbsEnergy_eq_sum_sub_diag]
  simp only [sub_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith only [hh]

end ContinuumTemperature
end

end OAI
