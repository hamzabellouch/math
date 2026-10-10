import OAI.Probability.ContinuumTransition.GenericGibbs

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

def latticeCell (z : Lattice) : Set Space := {x | cellIndex x = z}

theorem measurable_cellIndex : Measurable cellIndex := by
  apply Measurable.of_eval
  intro k
  exact ((EuclideanSpace.proj k).continuous.measurable.const_mul 4).floor

theorem measurableSet_latticeCell (z : Lattice) : MeasurableSet (latticeCell z) :=
  measurable_cellIndex (measurableSet_singleton z)

theorem gibbsEnergy_eq_pairSum (V : Space → Space → ℝ)
    (hV : ∀ x y, V x y = V y x) {ι : Type} [Fintype ι] [LinearOrder ι] (x : ι → Space) :
    gibbsEnergy V x = pairSum (fun i j => V (x i) (x j)) := by
  have hh := two_mul_pairSum (fun i j => V (x i) (x j)) (fun i j => hV (x i) (x j))
  unfold gibbsEnergy
  apply (div_eq_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  rw [mul_comm]
  convert hh.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp only [hij, ite_eq_left, ite_false]

theorem gibbsEnergy_sub (U W : Space → Space → ℝ) {ι : Type} [Fintype ι] (x : ι → Space) :
    gibbsEnergy (fun x y => U x y-W x y) x = gibbsEnergy U x-gibbsEnergy W x := by
  unfold gibbsEnergy
  have he (i j : ι) : (if i = j then 0 else U (x i) (x j)-W (x i) (x j)) =
      (if i = j then 0 else U (x i) (x j))-(if i = j then 0 else W (x i) (x j)) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  ring

theorem gibbsEnergy_nonneg (U : Space → Space → ℝ)
    (hU : ∀ x y, 0 ≤ U x y) {ι : Type} [Fintype ι] (x : ι → Space) :
    0 ≤ gibbsEnergy U x := by
  unfold gibbsEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · rfl
  · exact hU _ _

theorem gibbsEnergy_le_card_sq (W : Space → Space → ℝ) {ι : Type} [Fintype ι]
    (x : ι → Space) {J : ℝ} (hJ : 0 ≤ J) (hW : ∀ i j, W (x i) (x j) ≤ J) :
    gibbsEnergy W x ≤ J/2*(Fintype.card ι : ℝ)^2 := by
  have hh : (∑ i, ∑ j, if i = j then 0 else W (x i) (x j)) ≤
      ∑ _ : ι, ∑ _ : ι, J := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact hJ
    · exact hW i j
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  unfold gibbsEnergy
  nlinarith only [hh]

theorem core_gibbsEnergy_one_cell (t : ℝ) {ι : Type} [Fintype ι]
    (x : ι → Space) (z : Lattice) (hx : ∀ i, x i ∈ latticeCell z) :
    t^2/8*(Fintype.card ι : ℝ)^2-t^2/2*Fintype.card ι ≤
      gibbsEnergy (fun x y => coreProfile t ‖x-y‖) x := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [gibbsEnergy_eq_pairSum _ (fun x y => by rw [norm_sub_rev])]
  apply core_one_cell_bound
  intro i j
  exact dist_lt_one_of_cellIndex_eq ((hx i).trans (hx j).symm)

theorem physical_gibbs_moment_energy {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {ι : Type} [Fintype ι] (x : ι → Space) (z : Lattice) :
    (t^2/8)/4*(occupation (latticeCell z) x)^2 ≤
      gibbsEnergy (fun x y => physicalProfile t σ R ‖x-y‖) x+t^2/2*Fintype.card ι := by
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let S : Finset Lattice := insert z (Finset.univ.image (fun i => cellIndex (x i)))
  let c (i : ι) : S := ⟨cellIndex (x i), Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let k : S := ⟨z, Finset.mem_insert_self _ _⟩
  have hcard : (Fintype.card {i : ι // c i = k} : ℝ) = occupation (latticeCell z) x := by
    unfold occupation
    congr 1
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun i => by simp only [Subtype.ext_iff, c, k, latticeCell,
      mem_ofPred_eq])
  have hsq : (occupation (latticeCell z) x)^2 ≤
      ∑ j : S, (Fintype.card {i : ι // c i = j} : ℝ)^2 := by
    rw [← hcard]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : S => (Fintype.card {i : ι // c i = j} : ℝ)^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hp := physicalProfile_superstable ht hσ hR hs x c
    (fun j : S => (j : Lattice)) Subtype.val_injective (fun _ => rfl)
  rw [← gibbsEnergy_eq_pairSum (fun x y => physicalProfile t σ R ‖x-y‖)
    (fun x y => by rw [norm_sub_rev]) x] at hp
  have hcoef : (t^2/8)/4 ≤ t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2 := by
    nlinarith only [hsmall, sq_nonneg t]
  have h0 : 0 ≤ (t^2/8)/4 := by positivity
  have hb := (mul_le_mul_of_nonneg_left hsq h0).trans
    (mul_le_mul_of_nonneg_right hcoef (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  linarith only [hb, hp]

end ContinuumTemperature
end

end OAI
