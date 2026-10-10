import OAI.Probability.ContinuumTransition.TriangleGeometry

namespace OAI

universe u_1

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature
open Classical

def IsPacking (L : ℝ) (n : ℕ) : Prop :=
  ∃ x : Fin n → Space, (∀ i, x i ∈ cube L) ∧
    ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖

theorem isPacking_zero (L : ℝ) : IsPacking L 0 := by
  refine ⟨Fin.elim0, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

theorem packing_card_cubeCells {ι : Type u_1} [Fintype ι] {L : ℝ}
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) : Fintype.card ι ≤ (cubeCells L).card := by
  let f : ι → {k // k ∈ cubeCells L} := fun i =>
    ⟨cellIndex (x i), cellIndex_mem_cubeCells (hx i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hh := dist_lt_one_of_cellIndex_eq (congrArg Subtype.val hij)
    exact (not_lt_of_ge (hsep i j hne)) hh
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem IsPacking.card_bound {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ (cubeCells L).card := by
  obtain ⟨x,hx,hs⟩ := h
  simpa only [Fintype.card_fin] using packing_card_cubeCells x hx hs

noncomputable def packingNumber (L : ℝ) : ℕ :=
  Nat.findGreatest (IsPacking L) (cubeCells L).card

theorem packingNumber_realized (L : ℝ) : IsPacking L (packingNumber L) := by
  exact Nat.findGreatest_spec (show 0 ≤ (cubeCells L).card from Nat.zero_le _)
    (isPacking_zero L)

theorem IsPacking.le_packingNumber {L : ℝ} {n : ℕ} (h : IsPacking L n) :
    n ≤ packingNumber L := by
  exact Nat.le_findGreatest h.card_bound h

theorem card_le_packingNumber {ι : Type u_1} [Fintype ι] {L : ℝ}
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) : Fintype.card ι ≤ packingNumber L := by
  let e := Fintype.equivFin ι
  apply IsPacking.le_packingNumber
  exact ⟨fun i => x (e.symm i), fun i => hx _, fun i j hij => hsep _ _ (fun h => hij (e.symm.injective h))⟩

theorem packingNumber_bound {L : ℝ} (hL : 0 ≤ L) :
    (packingNumber L : ℝ) ≤ (4*L+2)^3 :=
  (Nat.cast_le.mpr (packingNumber_realized L).card_bound).trans (card_cubeCells_le hL)

theorem dilate_packing {ι : Type u_1} [Fintype ι] {L η : ℝ} (hη : 0 ≤ η)
    (x : ι → Space) (hx : ∀ i, x i ∈ cube L)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i-x j‖) :
    (∀ i, (1+η) • x i ∈ cube ((1+η)*L)) ∧
      ∀ i j, i ≠ j → 1+η ≤ ‖(1+η) • x i-(1+η) • x j‖ := by
  have he : 0 ≤ 1+η := by linarith
  constructor
  · intro i k
    have hi := hx i k
    change (1+η)*x i k ∈ Icc (-((1+η)*L)/2) (((1+η)*L)/2)
    have hlo := mul_le_mul_of_nonneg_left hi.1 he
    have hup := mul_le_mul_of_nonneg_left hi.2 he
    constructor <;> nlinarith only [hlo,hup]
  · intro i j hij
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg he]
    nlinarith only [mul_le_mul_of_nonneg_left (hsep i j hij) he]

theorem packingNumber_tiling {ℓ L : ℝ} (hℓ : 0 ≤ ℓ) (hL : 0 ≤ L) :
    tileCount ℓ L*packingNumber ℓ ≤ packingNumber L := by
  let κ := (Fin 3 → Fin ⌊L/(ℓ+2)⌋₊)
  obtain ⟨x,hx,hsep⟩ := packingNumber_realized ℓ
  let y : κ × Fin (packingNumber ℓ) → Space := fun i => x i.2+tileCenter ℓ L i.1
  have hy : ∀ i, y i ∈ cube L := by
    intro i
    have hk : (⌊L/(ℓ+2)⌋₊ : ℝ)*(ℓ+2) ≤ L :=
      (le_div_iff₀ (by linarith : 0 < ℓ+2)).1 (Nat.floor_le (div_nonneg hL (by linarith)))
    exact tileBox_subset hℓ hk i.1 ⟨_,hx _,rfl⟩
  have hs : ∀ i j, i ≠ j → 1 ≤ ‖y i-y j‖ := by
    intro i j hij
    by_cases he : i.1 = j.1
    · have hine : i.2 ≠ j.2 := fun h => hij (Prod.ext he h)
      simpa only [y, he, add_sub_add_right_eq_sub] using hsep i.2 j.2 hine
    · exact (by norm_num : (1 : ℝ) ≤ 2).trans (tileBox_separation hℓ he
        (show y i ∈ tileBox ℓ L i.1 from ⟨_,hx _,rfl⟩)
        (show y j ∈ tileBox ℓ L j.1 from ⟨_,hx _,rfl⟩))
  have hh := card_le_packingNumber y hy hs
  simpa only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, tileCount, κ] using hh

end ContinuumTemperature
end

end OAI
