import Mathlib

namespace OAI


namespace Problem355.PlaneReduction

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma intCast_sum_mul (q : ℕ) (x y : ι → ℤ) :
    ((∑ i, x i * y i : ℤ) : ZMod q) =
      ∑ i, (x i : ZMod q) * (y i : ZMod q) := by
  simp

theorem lift_orthogonal (q : ℕ) (x z : ι → ℤ)
    (hz : ∑ i, x i * z i = 1) (v : ι → ZMod q)
    (hv : ∑ i, (x i : ZMod q) * v i = 0) :
    ∃ w : ι → ℤ, (∑ i, x i * w i = 0) ∧
      ∀ i, (w i : ZMod q) = v i := by
  classical
  choose a ha using fun i => ZMod.intCast_surjective (v i)
  let t : ℤ := ∑ i, x i * a i
  have ht : (t : ZMod q) = 0 := by
    simpa [t, ha] using hv
  refine ⟨fun i => a i - t * z i, ?_, ?_⟩
  · calc
      (∑ i, x i * (a i - t * z i)) =
          (∑ i, x i * a i) - t * (∑ i, x i * z i) := by
            simp only [mul_sub, Finset.sum_sub_distrib,
              Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hz]; simp [t]
  · intro i
    simp [ht, ha]

theorem lift_orthogonal_scaled (q : ℕ) (x z : ι → ℤ)
    (hz : ∑ i, x i * z i = 1) (E : ℤ)
    (hE : IsUnit (E : ZMod q)) (v : ι → ZMod q)
    (hv : ∑ i, (x i : ZMod q) * v i = 0) :
    ∃ w : ι → ℤ, (∑ i, x i * w i = 0) ∧
      ∀ i, ((E * w i : ℤ) : ZMod q) = v i := by
  obtain ⟨u, hu⟩ := hE
  let v' : ι → ZMod q := fun i => (↑(u⁻¹) : ZMod q) * v i
  have hv' : ∑ i, (x i : ZMod q) * v' i = 0 := by
    calc
      (∑ i, (x i : ZMod q) * v' i) =
          (↑(u⁻¹) : ZMod q) * ∑ i, (x i : ZMod q) * v i := by
            simp only [v', Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hv, mul_zero]
  obtain ⟨w, hw, hred⟩ := lift_orthogonal q x z hz v' hv'
  refine ⟨w, hw, ?_⟩
  intro i
  rw [Int.cast_mul, hred, ← hu]
  simp [v', ← mul_assoc]

theorem lift_orthogonal_mem (q : ℕ) (x z : ι → ℤ)
    (hz : ∑ i, x i * z i = 1) (E : ℤ)
    (hE : IsUnit (E : ZMod q)) (Λ : Submodule ℤ (ι → ℤ))
    (hΛ : ∀ w : ι → ℤ, E • w ∈ Λ) (v : ι → ZMod q)
    (hv : ∑ i, (x i : ZMod q) * v i = 0) :
    ∃ w : ι → ℤ, w ∈ Λ ∧ (∑ i, x i * w i = 0) ∧
      ∀ i, (w i : ZMod q) = v i := by
  obtain ⟨w, hw, hred⟩ := lift_orthogonal_scaled q x z hz E hE v hv
  refine ⟨E • w, hΛ w, ?_, ?_⟩
  · change (∑ i, x i * (E * w i)) = 0
    calc
      (∑ i, x i * (E * w i)) = E * ∑ i, x i * w i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hw, mul_zero]
  · exact hred

theorem normal_reduction_ne_zero (q : ℕ) [Nontrivial (ZMod q)]
    (x z : ι → ℤ) (hz : ∑ i, x i * z i = 1) :
    (fun i => (x i : ZMod q)) ≠ 0 := by
  intro hx
  have hcast : (∑ i, (x i : ZMod q) * (z i : ZMod q)) = 1 := by
    simpa using congrArg (fun a : ℤ => (a : ZMod q)) hz
  have hxi : ∀ i, (x i : ZMod q) = 0 := fun i => congrFun hx i
  simp [hxi] at hcast

theorem annihilator_of_split_kernel {R : Type*} [CommRing R]
    (x z δ : ι → R) (hz : x ⬝ᵥ z = 1)
    (hδ : ∀ v : ι → R, x ⬝ᵥ v = 0 → δ ⬝ᵥ v = 0) :
    δ = (δ ⬝ᵥ z) • x := by
  apply dotProduct_eq
  intro v
  have hker : x ⬝ᵥ (v - (x ⬝ᵥ v) • z) = 0 := by
    simp [dotProduct_sub, dotProduct_smul, hz]
  have hd := hδ _ hker
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hd
  rw [smul_dotProduct, smul_eq_mul]
  exact (sub_eq_zero.mp hd).trans (mul_comm _ _)

theorem exists_in_kernel_not_annihilated_of_split {R : Type*} [CommRing R]
    (x z δ : ι → R) (hz : x ⬝ᵥ z = 1)
    (hδ : ∀ a : R, δ ≠ a • x) :
    ∃ v : ι → R, x ⬝ᵥ v = 0 ∧ δ ⬝ᵥ v ≠ 0 := by
  by_contra! h
  exact hδ _ (annihilator_of_split_kernel x z δ hz h)

theorem exists_in_kernel_not_annihilated {F : Type*} [Field F]
    (x δ : ι → F) (hx : x ≠ 0) (hδ : ∀ a : F, δ ≠ a • x) :
    ∃ v : ι → F, x ⬝ᵥ v = 0 ∧ δ ⬝ᵥ v ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  apply exists_in_kernel_not_annihilated_of_split x
    (Pi.single i (x i)⁻¹) δ _ hδ
  simp [dotProduct_single, hi]

end Problem355.PlaneReduction

end OAI
