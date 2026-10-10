import OAI.Analysis.TriangularHilbert.Switch

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section

lemma arrayCubic_eq (D : Finset ℤ) (A : Three → Matrix D D ℂ) (h : ℝ) :
    arrayCubic A h = h^2*(∑ v, ∑ i, ∑ j, ‖A v i j‖^3) := by
  simp only [arrayCubic,Finset.mul_sum]

lemma arrayCubic_mono {ι : Type uι} [Fintype ι] (A B : Three → Matrix ι ι ℂ)
    (hAB : ∀ v i j, ‖A v i j‖ ≤ ‖B v i j‖) (h : ℝ) : arrayCubic A h ≤ arrayCubic B h := by
  unfold arrayCubic
  apply Finset.sum_le_sum
  intro v _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  gcongr
  exact hAB v i j

lemma arrayCubic_replaceZero_le (D : Finset ℤ) (A : Three → Matrix D D ℂ) (B : Matrix D D ℂ)
    (hB : ∀ i j, ‖B i j‖ ≤ ‖A 0 i j‖) (h : ℝ) : arrayCubic (replaceZero A B) h ≤ arrayCubic A h := by
  apply arrayCubic_mono
  intro v i j
  by_cases hv : v=0
  · subst v; exact hB i j
  · simp [replaceZero,hv]

lemma finite_mesh_total_jumps_le (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (σ : ℕ → Three → ℝ) (hσ : ∀ k v, h^2 ≤ σ k v) :
    (∑ k ∈ Finset.range n,
      |totalPlaneEnergy (replaceZero A (B (k+1))) h (fun m => h*(m:ℤ)) 0 (σ k)-
        totalPlaneEnergy (replaceZero A (B k)) h (fun m => h*(m:ℤ)) 0 (σ k)|) ≤
      3*meshMassConstant*jumpScalarConstant*arrayCubic A h := by
  have hj := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    finite_mesh_energy_jump_le D A (B (k+1)) (B k) (hB (k+1)) (hB k) hh (hσ k))
  apply hj.trans
  rw [← Finset.mul_sum]
  have he : (∑ k ∈ Finset.range n, ∑ i : D, ∑ j : D, ‖B (k+1) i j-B k i j‖*jumpMax D A i j) =
      ∑ i : D, ∑ j : D, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖)*jumpMax D A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  rw [he]
  have hs : (∑ i : D, ∑ j : D, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖)*jumpMax D A i j) ≤
      2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have ht := mul_le_mul_of_nonneg_right (hvar i j) (jumpMax_nonneg D A i j)
    simpa only [mul_assoc] using ht
  have hz : 0 ≤ 3/2*meshMassConstant*h^2 := by have hm := meshMassConstant_pos; positivity
  calc
    _ ≤ (3/2*meshMassConstant*h^2)*(2*(∑ i : D, ∑ j : D, ‖A 0 i j‖*jumpMax D A i j)) := mul_le_mul_of_nonneg_left hs hz
    _ ≤ (3/2*meshMassConstant*h^2)*(2*(jumpScalarConstant*(∑ v, ∑ i, ∑ j, ‖A v i j‖^3))) := by
      gcongr
      exact sum_jumpMax_le D A
    _ = _ := by rw [arrayCubic_eq]; ring

lemma strictRate_ge_one (i v : Three) : 1 ≤ strictRate i v := by
  unfold strictRate; split_ifs <;> norm_num

def maskedConstant : ℝ := meshMassConstant*(2*Real.sqrt 2+3*jumpScalarConstant)

lemma maskedConstant_pos : 0 < maskedConstant := by
  unfold maskedConstant
  have hm := meshMassConstant_pos
  have hj := jumpScalarConstant_pos
  positivity

lemma finite_masked_dissipation (D : Finset ℤ) (A : Three → Matrix D D ℂ)
    (B : ℕ → Matrix D D ℂ) (hB : ∀ k i j, ‖B k i j‖ ≤ ‖A 0 i j‖) (n : ℕ)
    (hvar : ∀ i j, (∑ k ∈ Finset.range n, ‖B (k+1) i j-B k i j‖) ≤ 2*‖A 0 i j‖)
    {h : ℝ} (hh : 0 < h) (t : ℕ → ℝ) (ht : Monotone t) (ht0 : h^2 ≤ t 0) (r : Three) :
    strictConstant * (∑ k ∈ Finset.range n,
      ∫ s in t k..t (k+1), ∑ v, planeIntegral (fun p => heatCost (replaceZero A (B k)) h
        (fun m => h*(m:ℤ)) p (fun z => strictRate r z*s) v v) 0) ≤ maskedConstant*arrayCubic A h := by
  have htpos (k : ℕ) : 0 < t k := (sq_pos_of_pos hh).trans_le (ht0.trans (ht (Nat.zero_le _)))
  have hσ (k : ℕ) (v : Three) : h^2 ≤ strictRate r v*t k :=
    (ht0.trans (ht (Nat.zero_le _))).trans (le_mul_of_one_le_left (htpos k).le (strictRate_ge_one r v))
  have hi := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) =>
    integrated_strict_dissipation (replaceZero A (B k)) hh (fun m => h*(m:ℤ)) 0 r
      (htpos k) (ht (Nat.le_succ k)))
  rw [← Finset.mul_sum] at hi
  apply hi.trans
  let E : ℕ → ℕ → ℝ := fun k l => totalPlaneEnergy (replaceZero A (B k)) h (fun m => h*(m:ℤ)) 0
    (fun v => strictRate r v*t l)
  have htel := telescope_with_jumps E n (totalPlaneEnergy_nonneg _ _ _ _ _)
  apply htel.trans
  have hin := (finite_mesh_totalPlaneEnergy_le D (replaceZero A (B 0)) hh 0 (hσ 0)).trans
    (mul_le_mul_of_nonneg_left (arrayCubic_replaceZero_le D A (B 0) (hB 0) h) (by have hm := meshMassConstant_pos; positivity))
  have hj := finite_mesh_total_jumps_le D A B hB n hvar hh (fun k v => strictRate r v*t (k+1)) (fun k v => hσ (k+1) v)
  change E 0 0 ≤ _ at hin
  change (∑ k ∈ Finset.range n, |E (k+1) (k+1)-E k (k+1)|) ≤ _ at hj
  apply (add_le_add hin hj).trans_eq
  unfold maskedConstant
  ring
end
end TriangularHilbert.Heat
end

end OAI
