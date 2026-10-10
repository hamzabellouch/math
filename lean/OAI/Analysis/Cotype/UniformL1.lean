import OAI.Analysis.Cotype.VectorWalsh
import Mathlib.Data.Fintype.EquivFin

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def L1Family {ι : Type*} [Fintype ι] (x : ι → X) (c : ℝ) : Prop :=
  (∀ i, ‖x i‖ ≤ 1) ∧ ∀ a : ι → ℝ, c * ∑ i, |a i| ≤ ‖∑ i, a i • x i‖

def UniformL1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ x : Fin n → X, L1Family x c

theorem L1Family.upper {ι : Type*} [Fintype ι] {x : ι → X} {c : ℝ}
    (h : L1Family x c) (a : ι → ℝ) : ‖∑ i, a i • x i‖ ≤ ∑ i, |a i| := by
  classical
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (h.1 i)))

theorem L1Family.reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) {x : ι → X} {c : ℝ} (h : L1Family x c) :
    L1Family (fun i => x (e i)) c := by
  refine ⟨fun i => h.1 (e i), fun a => ?_⟩
  have hl := h.2 (fun i => a (e.symm i))
  simpa only [← e.sum_comp, e.symm_apply_apply] using hl

theorem L1Family.restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (j : κ ↪ ι) {x : ι → X} {c : ℝ} (h : L1Family x c) :
    L1Family (fun i => x (j i)) c := by
  classical
  refine ⟨fun i => h.1 (j i), fun a => ?_⟩
  let b : ι → ℝ := Function.extend j a (fun _ => 0)
  have hb (i : κ) : b (j i) = a i := j.injective.extend_apply _ _ _
  have hz (i : ι) (hi : i ∉ Finset.univ.image j) : b i = 0 := by
    apply Function.extend_apply'
    simpa using hi
  have hscalar : (∑ i, |b i|) = ∑ i, |a i| := by
    calc
      _ = ∑ i ∈ Finset.univ.image j, |b i| :=
        (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [hz i hi, abs_zero])).symm
      _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hb]
  have hvector : (∑ i, b i • x i) = ∑ i, a i • x (j i) := by
    calc
      _ = ∑ i ∈ Finset.univ.image j, b i • x i :=
        (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by rw [hz i hi, zero_smul])).symm
      _ = _ := by rw [Finset.sum_image (fun _ _ _ _ he => j.injective he)]; simp only [hb]
  have hl := h.2 b
  rw [hscalar, hvector] at hl
  exact hl

theorem uniformL1_iff_cube : UniformL1 X ↔
    ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X, L1Family x L⁻¹ := by
  constructor
  · rintro ⟨c,hc,h⟩
    refine ⟨c⁻¹,inv_pos.mpr hc,fun n => ?_⟩
    obtain ⟨x,hx⟩ := h (Fintype.card (Cube n))
    exact ⟨fun i => x ((Fintype.equivFin (Cube n)) i), by
      simpa using hx.reindex (Fintype.equivFin (Cube n))⟩
  · rintro ⟨L,hL,h⟩
    refine ⟨L⁻¹,inv_pos.mpr hL,fun n => ?_⟩
    obtain ⟨x,hx⟩ := h n
    have hc : Fintype.card (Fin n) ≤ Fintype.card (Cube n) := by
      simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
      have hn : n < 2^n := Nat.lt_two_pow_self
      omega
    let j : Fin n ↪ Cube n := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
    exact ⟨fun i => x (j i), hx.restrict j⟩

theorem not_uniformL1_of_no_cube
    (h : ¬ ∃ L : ℝ, 0 < L ∧ ∀ n : ℕ, ∃ x : Cube n → X,
      (∀ u, ‖x u‖ ≤ 1) ∧
      (∀ a : Cube n → ℝ, L⁻¹ * ∑ u, |a u| ≤ ‖∑ u, a u • x u‖)) :
    ¬ UniformL1 X := fun hu => h (uniformL1_iff_cube.mp hu)

end Cotype

end

end OAI
