import Mathlib

namespace OAI

section
noncomputable section
open scoped Classical BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {I X : Type*}

lemma finite_incidence_sum (J : Finset I) (L : I → Finset X) (B : Finset X)
    (hsub : ∀ j∈J, L j⊆B) (f : X → ℝ) :
    (∑ j∈J, ∑ x∈L j, f x) =
      ∑ x∈B, ((J.filter (fun j => x∈L j)).card:ℝ)*f x := by
  have he (j : I) (hj : j∈J) : (∑ x∈L j, f x)=∑ x∈B, if x∈L j then f x else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨hsub j hj hx,hx⟩,fun hx => hx.2⟩
  calc
    _ = ∑ j∈J, ∑ x∈B, if x∈L j then f x else 0 := Finset.sum_congr rfl he
    _ = ∑ x∈B, ∑ j∈J, if x∈L j then f x else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [←Finset.sum_filter]
      simp

lemma sum_le_sum_of_finite_cover (J : Finset I) (L : I → Finset X)
    (F : Finset X) (hcover : ∀ x∈F, ∃ j∈J, x∈L j)
    (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ x∈F, f x)≤∑ j∈J, ∑ x∈L j, f x := by
  let B := F∪J.biUnion L
  have hJB : ∀ j∈J, L j⊆B := by
    intro j hj x hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hx⟩)
  rw [finite_incidence_sum J L B hJB f]
  calc
    _ ≤ ∑ x∈F, ((J.filter (fun j => x∈L j)).card:ℝ)*f x := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨j,hj,hxj⟩ := hcover x hx
      have hp : 1≤(J.filter (fun j => x∈L j)).card :=
        Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hxj⟩⟩
      have hp' : (1:ℝ)≤(J.filter (fun j => x∈L j)).card := by exact_mod_cast hp
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp' (hf x)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by
      intro x hx hxn
      exact mul_nonneg (Nat.cast_nonneg _) (hf x))

lemma sum_le_sum_of_finite_overlap (J : Finset I) (L : I → Finset X)
    (B : Finset X) (hsub : ∀ j∈J, L j⊆B) (K : ℕ)
    (hover : ∀ x∈B, (J.filter (fun j => x∈L j)).card≤K)
    (f : X → ℝ) (hf : ∀ x, 0≤f x) :
    (∑ j∈J, ∑ x∈L j, f x)≤(K:ℝ)*(∑ x∈B, f x) := by
  rw [finite_incidence_sum J L B hsub f,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hover x hx)) (hf x)

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
