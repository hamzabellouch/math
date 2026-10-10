import OAI.Probability.ContinuumTransition.GibbsQuadratic

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem gibbsEnergy_mul_left (V : Space → Space → ℝ) (a : ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => a*V x y) x = a*gibbsEnergy V x := by
  have he (i j : ι) : (if i = j then 0 else a*V (x i) (x j)) =
      a*(if i = j then 0 else V (x i) (x j)) := by split_ifs <;> ring
  simp only [gibbsEnergy, he, ← Finset.mul_sum]
  ring

theorem gibbsEnergy_block_constant {q : ℕ} (hq : 0 < q) (γ : ℝ)
    {ι : Type} [Fintype ι] (s : Finset Lattice) (c : ι → s) (x : ι → Space)
    (hx : ∀ i, x i ∈ gridBox ((q : ℝ)/4) (c i)) :
    gibbsEnergy (blockCut q (fun _ _ => γ)) x =
      γ*((∑ k : s, (Fintype.card {i // c i = k} : ℝ)^2)-Fintype.card ι)/2 := by
  have hu : 0 < (q : ℝ)/4 := by positivity
  have he (i j : ι) : blockCut q (fun _ _ => γ) (x i) (x j) = if c i = c j then γ else 0 := by
    simp only [blockCut, (mem_gridBox_iff hu _ _).1 (hx i),
      (mem_gridBox_iff hu _ _).1 (hx j), Subtype.coe_inj]
  rw [gibbsEnergy_eq_sum_sub_diag]
  simp only [he, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [double_sum_comp_eq c (fun k l => if k = l then γ else 0)]
  have hs : (∑ k : s, ∑ l : s, (if k = l then γ else 0)*
      (Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ)) =
      γ*∑ k : s, (Fintype.card {i // c i = k} : ℝ)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [hs]
  ring

theorem quadraticBlock_eq_sub (q : ℕ) (φ : ℝ → ℝ) (γ : ℝ) :
    quadraticBlock q φ γ = fun x y => blockCut q (fun x y => φ ‖x-y‖) x y-
      blockCut q (fun _ _ => γ) x y := by
  funext x y
  unfold quadraticBlock blockCut
  split_ifs <;> ring

theorem kac_gibbsFamily_le_quadratic {C : NNReal} (hC : LipschitzWith C kernel)
    {R β a μ : ℝ} (hR : 0 < R) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    {q : ℕ} (hq : 0 < q) (φ : ℝ → ℝ)
    {ι : Type} [Fintype ι] (s : Finset Lattice) (c : ι → s) (x : ι → Space)
    (hx : ∀ i, x i ∈ gridBox ((q : ℝ)/4) (c i)) :
    let u := (q : ℝ)/4
    let γ := a*(1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3)/u^3
    gibbsFamily (fun x y => blockCut q (fun x y => φ ‖x-y‖) x y-a*scaledKernel R (x-y)) β μ ι x ≤
      gibbsFamily (quadraticBlock q φ γ) β (μ+β*γ/2) ι x := by
  dsimp only
  let u := (q : ℝ)/4
  let γ := a*(1+(6*(C : ℝ)*u/R^4)*(2*(R+6*u))^3)/u^3
  have hu : 0 < u := by dsimp only [u]; positivity
  have he := kac_energy_upper hC hR hu s c x hx
  have hb : a*gibbsEnergy (fun x y => scaledKernel R (x-y)) x ≤
      γ/2*∑ k : s, (Fintype.card {i // c i = k} : ℝ)^2 := by
    apply (mul_le_mul_of_nonneg_left he ha).trans_eq
    dsimp only [γ]
    ring
  unfold gibbsFamily
  split_ifs
  · rw [gibbsEnergy_sub, gibbsEnergy_mul_left, quadraticBlock_eq_sub,
      gibbsEnergy_sub, gibbsEnergy_block_constant hq γ s c x hx]
    apply Real.exp_le_exp.mpr
    change μ*(Fintype.card ι : ℝ)-β*(_-a*_) ≤
      (μ+β*γ/2)*(Fintype.card ι : ℝ)-β*(_-γ*(_-Fintype.card ι)/2)
    nlinarith only [mul_le_mul_of_nonneg_left hb hβ]
  · rfl

end ContinuumTemperature
end

end OAI
