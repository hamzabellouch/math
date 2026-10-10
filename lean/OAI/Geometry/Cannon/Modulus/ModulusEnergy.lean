import Mathlib
import OAI.Geometry.Cannon.Modulus.Cost

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCells

open CannonDuality Set Filter

variable {X ι J : Type*} [Fintype ι] [Fintype J]

lemma modulus_le_energy (C : ι → Set X) (F : Set (Set X)) (w : Weights ι)
    (hw : Admissible (familyVectors C F : Set (Weights ι)) w) :
    modulus C F ≤ ‖w‖^2 := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro a ⟨v,_,rfl⟩
    exact sq_nonneg _
  · exact ⟨w,hw,rfl⟩

theorem modulus_le_card_mul_sum (C : ι → Set X)
    (hC : ∀ x, ∃ i, x ∈ C i) (F : Set (Set X)) (H : J → Set (Set X))
    (hH : ∀ j, (H j).Nonempty) (hHn : ∀ j A, A ∈ H j → A.Nonempty)
    (hsub : ∀ A ∈ F, ∃ j, ∃ B ∈ H j, B ⊆ A) :
    modulus C F ≤ Fintype.card J * ∑ j, modulus C (H j) := by
  classical
  choose w hw hwe using fun j => (modulus_minimum C hC (hH j) (hHn j)).2
  have hwp (j : J) : Nonnegative (w j) := (hw j).1
  let W : Weights ι := ∑ j, w j
  have hW : Admissible (familyVectors C F : Set (Weights ι)) W := by
    rw [admissible_iff]
    have hpoint (i : ι) : W i = ∑ j, w j i := by simp [W]
    have hnon : Nonnegative W := by
      intro i
      rw [hpoint]
      exact Finset.sum_nonneg (fun j _ => hwp j i)
    refine ⟨hnon,?_⟩
    intro A hA
    obtain ⟨j,B,hB,hBA⟩ := hsub A hA
    have hwj := (admissible_iff C (H j) (w j)).mp (hw j)
    calc
      1 ≤ ∑ i ∈ indices C B, w j i := hwj.2 B hB
      _ ≤ ∑ i ∈ indices C A, w j i := Finset.sum_le_sum_of_subset_of_nonneg
        (indices_mono C hBA) (fun i _ _ => hwp j i)
      _ ≤ ∑ i ∈ indices C A, W i := by
        apply Finset.sum_le_sum
        intro i _
        rw [hpoint]
        exact Finset.single_le_sum (fun k _ => hwp k i) (Finset.mem_univ j)
  calc
    modulus C F ≤ ‖W‖^2 := modulus_le_energy C F W hW
    _ ≤ (∑ j, ‖w j‖)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg W)
      exact norm_sum_le _ _
    _ ≤ (Fintype.card J : ℝ)*∑ j, ‖w j‖^2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖w j‖))
    _ = _ := by simp only [hwe]

theorem exists_modulus_localization [Nonempty J] (C : ι → Set X)
    (hC : ∀ x, ∃ i, x ∈ C i) (F : Set (Set X)) (H : J → Set (Set X))
    (hH : ∀ j, (H j).Nonempty) (hHn : ∀ j A, A ∈ H j → A.Nonempty)
    (hsub : ∀ A ∈ F, ∃ j, ∃ B ∈ H j, B ⊆ A) :
    ∃ j, modulus C F ≤ (Fintype.card J : ℝ)^2 * modulus C (H j) := by
  obtain ⟨j,_,hj⟩ := Finset.univ.exists_max_image (fun j => modulus C (H j)) Finset.univ_nonempty
  refine ⟨j,(modulus_le_card_mul_sum C hC F H hH hHn hsub).trans ?_⟩
  calc
    (Fintype.card J : ℝ)*∑ k, modulus C (H k) ≤
        (Fintype.card J : ℝ)*∑ _k : J, modulus C (H j) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => hj k hk))
      exact Nat.cast_nonneg _
    _ = _ := by simp [pow_two,mul_assoc]

theorem fixed_localization_subsequence (M : ℕ → ℝ) (m : J → ℕ → ℝ) (C : ℝ)
    (h : ∀ n, ∃ j, M n ≤ C*m j n) :
    ∃ j, ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ n, M (N n) ≤ C*m j (N n) := by
  have hf : ∃ᶠ n in atTop, ∃ j, M n ≤ C*m j n :=
    (Eventually.of_forall h).frequently
  obtain ⟨j,hj⟩ := frequently_exists.mp hf
  obtain ⟨N,hN,hNj⟩ := extraction_of_frequently_atTop hj
  exact ⟨j,N,hN,hNj⟩

end CannonCells

end
end
end
end
end
end
end
end
end

end OAI
