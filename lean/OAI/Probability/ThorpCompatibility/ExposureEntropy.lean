import Mathlib
import OAI.Probability.ThorpCompatibility.HeavyEntries

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma cellRows_weight_sum {α β : Type*} [Fintype α] [Fintype β]
    (r : α → Equiv.Perm β) (v : β × β → ℝ) :
    (∑ i : α, ∑ j : β, v (j, r i j)) =
      ∑ b : β × β, (cellRows r b).card * v b := by
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ i : α, ∑ k : β, if r i j = k then v (j,k) else 0 := by simp
    _ = ∑ k : β, ∑ i : α, if r i j = k then v (j,k) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have he : (∑ i : α, if r i j = k then v (j,k) else 0) =
          ∑ _i ∈ cellRows r (j,k), v (j,k) := by
        rw [cellRows, Finset.sum_filter]
      rw [he]
      simp

lemma clumpCount_eq_entries {A D : ℕ} (K : ℝ) (a : Grid A D) :
    (∑ k : Fin D, ∑ i : Fin A, if K < (entryClumpSize k i a : ℝ) then 1 else 0) =
      (clumpCount K a.1 : ℝ) := by
  rw [Finset.sum_comm]
  have he (i : Fin A) :
      (∑ k : Fin D, if K < (entryClumpSize k i a : ℝ) then (1 : ℝ) else 0) =
      ∑ j : Fin D, if K < ((cellRows a.1 (j, a.1 i j)).card : ℝ) then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv (a.1 i).symm
    intro k
    simp only [entryClumpSize, Equiv.apply_symm_apply]
    by_cases hk : K < ((cellRows a.1 ((a.1 i).symm k, k)).card : ℝ) <;> simp [hk]
  simp_rw [he]
  rw [cellRows_weight_sum a.1
    (fun b => if K < ((cellRows a.1 b).card : ℝ) then (1 : ℝ) else 0)]
  unfold clumpCount
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

lemma mean_clumpCount_eq_entries {A D : ℕ} (Q : Law (Grid A D)) (K : ℝ) :
    (∑ k : Fin D, ∑ i : Fin A,
      Q.mean (fun a => if K < (entryClumpSize k i a : ℝ) then 1 else 0)) =
      Q.mean (fun a => (clumpCount K a.1 : ℝ)) := by
  rw [show Q.mean (fun a => (clumpCount K a.1 : ℝ)) =
      Q.mean (fun a => ∑ k : Fin D, ∑ i : Fin A,
        if K < (entryClumpSize k i a : ℝ) then 1 else 0) by
    congr 1
    funext a
    exact (clumpCount_eq_entries K a).symm]
  simp_rw [Law.mean_sum]

noncomputable def totalExposureError (A D : ℕ) (H K : ℝ) : ℝ :=
  A * (1 + Real.log (D : ℝ)) +
    2 * D * K * H * (1 + Real.log (D : ℝ)) * (harmonic A : ℝ)

lemma sum_exposureError {A D : ℕ} (hD : 0 < D) (H K : ℝ) :
    (∑ _ : Fin D, ∑ i : Fin A, exposureError A D H K i) =
      totalExposureError A D H K := by
  have he (i : Fin A) : exposureError A D H K i =
      (1 + Real.log (D : ℝ)) / D +
      (2 * K * H * (1 + Real.log (D : ℝ))) * (1 / ((A - (i : ℕ) : ℕ) : ℝ)) := by
    unfold exposureError
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_inv_sub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold totalExposureError
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  field_simp [hD0]

lemma grid_entropy_charge {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (A : ℝ) * D - totalExposureError A D H K -
      3 * (∑ k : Fin D, ∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)) -
      Q.mean (fun a => (clumpCount K a.1 : ℝ)) ≤
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy := by
  let E : Law (Equiv.Perm (Fin D)) := Law.uniform
  have hl := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) =>
      mean_columnCost_lower hD Q hQ hH hK k i))
  have hu (e : Equiv.Perm (Fin D)) :
      (∑ k : Fin D, ∑ i : Fin A, Q.mean (columnCost Q H e k i)) ≤
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy := by
    rw [← grid_comparison_sum Q e]
    exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun i _ =>
      columnCost_le_comparison Q hQ H e k i))
  have havg := E.mean_mono hu
  rw [Law.mean_const] at havg
  simp only [Law.mean_sum] at havg
  have hh := le_trans hl havg
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  rw [mean_clumpCount_eq_entries] at hh
  have herr := sum_exposureError (A := A) (by omega : 0 < D) H K
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at herr
  rw [herr] at hh
  nlinarith

lemma grid_deficit_decomposition {A D : ℕ} (Q : Law (Grid A D)) :
    Q.uniformDeficit = (Q.map Prod.fst).uniformDeficit +
      (∑ k : Fin D, (Q.map (fun a => a.2 k)).uniformDeficit) +
        ((Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy) := by
  simp only [Law.uniformDeficit_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : Real.log (Fintype.card (Grid A D) : ℝ) =
      Real.log (Fintype.card (Rows A D) : ℝ) + D * Real.log (Fintype.card (Equiv.Perm (Fin A)) : ℝ) := by
    have h₁ : (Fintype.card (Rows A D) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h₂ : ((Fintype.card (Equiv.Perm (Fin A)) : ℝ) ^ D) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
    change Real.log (Fintype.card (Rows A D × Cols A D) : ℝ) = _
    rw [Fintype.card_prod, Nat.cast_mul, Real.log_mul h₁ (by
      change (Fintype.card (Fin D → Equiv.Perm (Fin A)) : ℝ) ≠ 0
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      exact h₂)]
    congr 1
    change Real.log (Fintype.card (Fin D → Equiv.Perm (Fin A)) : ℝ) = _
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  rw [hc]
  ring

end ThorpCompatibility

end OAI
