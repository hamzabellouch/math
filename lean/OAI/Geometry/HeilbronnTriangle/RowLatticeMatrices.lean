import OAI.Geometry.HeilbronnTriangle.PlaneRowTransport

namespace OAI


noncomputable section

namespace Problem355.RowLatticeMatrices

open Matrix IntegralPlaneLattice

abbrev IntMatrix := Matrix (Fin 3) (Fin 3) ℤ

abbrev RowMatrices (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :=
  {A : IntMatrix // A *ᵥ x = 0 ∧ ∀ i, A i ∈ L}

def rowsEquiv (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ)) :
    RowMatrices x L ≃ (Fin 3 → latticeIn x L) where
  toFun A i := kernelEquivIn x L ⟨A.val i, A.property.2 i, by
    change x ⬝ᵥ A.val i = 0
    rw [dotProduct_comm]
    exact congrFun A.property.1 i⟩
  invFun u := ⟨fun i => ((kernelEquivIn x L).symm (u i)).val, by
    constructor
    · funext i
      change (((kernelEquivIn x L).symm (u i)).val) ⬝ᵥ x = 0
      rw [dotProduct_comm]
      exact ((kernelEquivIn x L).symm (u i)).property.2
    · intro i
      exact ((kernelEquivIn x L).symm (u i)).property.1⟩
  left_inv A := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((kernelEquivIn x L).symm_apply_apply
      ⟨A.val i, A.property.2 i, by
        change x ⬝ᵥ A.val i = 0
        rw [dotProduct_comm]
        exact congrFun A.property.1 i⟩)
  right_inv u := by
    funext i
    exact (kernelEquivIn x L).apply_symm_apply (u i)

@[simp] theorem rowsEquiv_coordinate (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i j : Fin 3) :
    (((rowsEquiv x L A i : plane x) : Ambient) j) = (A.val i j : ℝ) := rfl

@[simp] theorem rowsEquiv_norm (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i : Fin 3) :
    ‖rowsEquiv x L A i‖ = ‖castVec (A.val i)‖ := rfl

theorem rowsEquiv_independent_of_minor (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i j s t : Fin 3)
    (hm : A.val i s * A.val j t - A.val i t * A.val j s ≠ 0) :
    LinearIndependent ℝ ![(rowsEquiv x L A i : plane x),
      (rowsEquiv x L A j : plane x)] := by
  exact PlaneRowTransport.rows_pair_linearIndependent_of_minor x
    ⟨A.val, A.property.1⟩ i j s t hm

theorem rowsEquiv_independent_of_projections (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (s t : Fin 3)
    (hs : A.val 2 s ≠ 0) (ht : A.val 2 t ≠ 0)
    (hne : PlaneRowTransport.projectedColumn A.val s ≠
      PlaneRowTransport.projectedColumn A.val t) :
    ∃ i j : Fin 3, LinearIndependent ℝ ![(rowsEquiv x L A i : plane x),
      (rowsEquiv x L A j : plane x)] := by
  obtain ⟨i, _, hi⟩ := PlaneRowTransport.exists_minor_of_projected_columns_ne
    A.val s t hs ht hne
  exact ⟨i, 2, rowsEquiv_independent_of_minor x L A i 2 s t hi⟩

theorem rowsEquiv_norm_le_four_mul (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (A : RowMatrices x L) (i : Fin 3)
    {N : ℝ} (hN : 0 ≤ N) (hA : ∀ j, |(A.val i j : ℝ)| ≤ 2 * N) :
    ‖rowsEquiv x L A i‖ ≤ 4 * N := by
  exact PlaneRowTransport.norm_rows_le_four_mul x ⟨A.val, A.property.1⟩ i hN hA

def rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L) :
    Finset (Fin 3 → latticeIn x L) := by
  classical
  exact S.attach.image (fun A => rowsEquiv x L ⟨A.val, hS A.val A.property⟩)

@[simp] theorem mem_rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (u : Fin 3 → latticeIn x L) :
    u ∈ rowFamily x L S hS ↔ ((rowsEquiv x L).symm u).val ∈ S := by
  classical
  constructor
  · intro hu
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hu
    simp
  · intro hu
    apply Finset.mem_image.mpr
    refine ⟨⟨((rowsEquiv x L).symm u).val, hu⟩, Finset.mem_attach _ _, ?_⟩
    change rowsEquiv x L ((rowsEquiv x L).symm u) = u
    exact (rowsEquiv x L).apply_symm_apply u

theorem card_rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L) :
    (rowFamily x L S hS).card = S.card := by
  classical
  rw [rowFamily, Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro A B h
    apply Subtype.ext
    exact congrArg (fun M : RowMatrices x L => M.val) ((rowsEquiv x L).injective h)

theorem sum_rowFamily (x : Fin 3 → ℤ) (L : Submodule ℤ (Fin 3 → ℤ))
    (S : Finset IntMatrix) (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (W : IntMatrix → ℝ) :
    ∑ u ∈ rowFamily x L S hS, W ((rowsEquiv x L).symm u).val =
      ∑ A ∈ S, W A := by
  classical
  rw [rowFamily, Finset.sum_image]
  · simp only [Equiv.symm_apply_apply]
    exact Finset.sum_attach S W
  · intro A hA B hB h
    apply Subtype.ext
    exact congrArg (fun M : RowMatrices x L => M.val) ((rowsEquiv x L).injective h)

theorem rowFamily_norm_le_four_mul (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (S : Finset IntMatrix)
    (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    {N : ℝ} (hN : 0 ≤ N)
    (hbound : ∀ A ∈ S, ∀ i j, |(A i j : ℝ)| ≤ 2 * N) :
    ∀ u ∈ rowFamily x L S hS, ∀ i, ‖(u i : plane x)‖ ≤ 4 * N := by
  intro u hu i
  have hm := (mem_rowFamily x L S hS u).mp hu
  have h := rowsEquiv_norm_le_four_mul x L ((rowsEquiv x L).symm u) i hN
    (hbound _ hm i)
  change ‖u i‖ ≤ 4 * N
  simpa only [Equiv.apply_symm_apply] using h

theorem rowFamily_independent_of_projections (x : Fin 3 → ℤ)
    (L : Submodule ℤ (Fin 3 → ℤ)) (S : Finset IntMatrix)
    (hS : ∀ A ∈ S, A *ᵥ x = 0 ∧ ∀ i, A i ∈ L)
    (hproj : ∀ A ∈ S, ∃ s t : Fin 3, A 2 s ≠ 0 ∧ A 2 t ≠ 0 ∧
      PlaneRowTransport.projectedColumn A s ≠ PlaneRowTransport.projectedColumn A t) :
    ∀ u ∈ rowFamily x L S hS, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(u i : plane x), (u j : plane x)] := by
  intro u hu
  have hm := (mem_rowFamily x L S hS u).mp hu
  obtain ⟨s, t, hs, ht, hne⟩ := hproj _ hm
  have h := rowsEquiv_independent_of_projections x L ((rowsEquiv x L).symm u)
    s t hs ht hne
  simpa only [Equiv.apply_symm_apply] using h

end Problem355.RowLatticeMatrices

end

end OAI
