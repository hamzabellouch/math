import OAI.Analysis.HyperbolicCones.PencilConjugation
import OAI.Analysis.HyperbolicCones.PencilKernel

namespace OAI

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

theorem pencil_compression {n : ℕ} (L : V →ₗ[ℝ] Sym n) (e : V)
    (he : (L e : Mat n ℝ).PosSemidef)
    (hker : ∀ x : V, ∀ v : Fin n → ℝ,
      (L e : Mat n ℝ) *ᵥ v = 0 → (L x : Mat n ℝ) *ᵥ v = 0) :
    ∃ m : ℕ, ∃ C : V →ₗ[ℝ] Sym m,
      (C e : Mat m ℝ).PosDef ∧
      ∀ x : V, (L x : Mat n ℝ).PosSemidef ↔ (C x : Mat m ℝ).PosSemidef := by
  classical
  let p : Fin n → Prop := fun i => 0 < (sym_isHermitian (L e)).eigenvalues i
  let J := {i : Fin n // p i}
  let m := Fintype.card J
  let q : Fin m ≃ J := (Fintype.equivFin J).symm
  let f : Fin m → Fin n := fun i => (q i).val
  let U : Mat n ℝ := (sym_isHermitian (L e)).eigenvectorUnitary
  let T := conjugatePencil L U
  let C := restrictPencil T f
  have hf : Function.Injective f := Subtype.val_injective.comp q.injective
  refine ⟨m, C, ?_, ?_⟩
  · change ((Uᴴ * (L e : Mat n ℝ) * U).submatrix f f).PosDef
    rw [spectral_conjugate_diagonal (L e), Matrix.submatrix_diagonal _ f hf]
    exact Matrix.PosDef.diagonal fun i => (q i).property
  · intro x
    have hT : (T x : Mat n ℝ).IsHermitian := (T x).property
    have hzero : ∀ i, ¬p i → ∀ j, (T x : Mat n ℝ) i j = 0 := by
      intro i hi j
      exact spectral_conjugate_zero_row (L e) (L x) he (hker x) i hi j
    have hp := matrix_compression_posSemidef_iff p (T x : Mat n ℝ) hT hzero
    have hq := Matrix.posSemidef_submatrix_equiv
      (M := (T x : Mat n ℝ).submatrix (Subtype.val : J → Fin n) Subtype.val) q
    calc
      (L x : Mat n ℝ).PosSemidef ↔ (T x : Mat n ℝ).PosSemidef :=
        (conjugatePencil_posSemidef_iff L U
          (Unitary.isUnit_coe (U := (sym_isHermitian (L e)).eigenvectorUnitary)) x).symm
      _ ↔ ((T x : Mat n ℝ).submatrix (Subtype.val : J → Fin n) Subtype.val).PosSemidef := hp
      _ ↔ (C x : Mat m ℝ).PosSemidef := by
        simpa [C, restrictPencil, f, Matrix.submatrix_submatrix, Function.comp_def] using hq.symm

theorem pencil_compression_positive {n : ℕ} (L : V →ₗ[ℝ] Sym n) (e : V)
    (he : (L e : Mat n ℝ).PosSemidef)
    (hker : ∀ x : V, ∀ v : Fin n → ℝ,
      (L e : Mat n ℝ) *ᵥ v = 0 → (L x : Mat n ℝ) *ᵥ v = 0)
    (hproper : ∃ x : V, ¬(L x : Mat n ℝ).PosSemidef) :
    ∃ m : ℕ, 0 < m ∧ ∃ C : V →ₗ[ℝ] Sym m,
      (C e : Mat m ℝ).PosDef ∧
      ∀ x : V, (L x : Mat n ℝ).PosSemidef ↔ (C x : Mat m ℝ).PosSemidef := by
  obtain ⟨m, C, hC, hrep⟩ := pencil_compression L e he hker
  refine ⟨m, ?_, C, hC, hrep⟩
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  obtain ⟨x, hx⟩ := hproper
  apply hx
  apply (hrep x).mpr
  have hz : (C x : Mat 0 ℝ) = 0 := Subsingleton.elim _ _
  rw [hz]
  exact Matrix.PosSemidef.zero

end Paper256

end

end OAI
