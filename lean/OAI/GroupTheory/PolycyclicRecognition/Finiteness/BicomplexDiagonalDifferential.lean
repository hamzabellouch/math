import OAI.GroupTheory.PolycyclicRecognition.Finiteness.BicomplexDiagonal

namespace OAI

/-! # The total differential in finite antidiagonal coordinates -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] ModuleCat.isModule
attribute [local instance 2300] Pi.module

variable {R : Type} [CommRing R] (K : NatBicomplex R)

def bicomplexDiagonalDifferential (n : ℕ) :
    bicomplexDiagonal K (n + 1) →ₗ[R] bicomplexDiagonal K n :=
  (bicomplexToDiagonal K n).comp
    (((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom.comp
      (bicomplexFromDiagonal K (n + 1)))

theorem bicomplexToDiagonal_d (n : ℕ)
    (x : (K.total (ComplexShape.down ℕ)).X (n + 1)) :
    bicomplexToDiagonal K n (((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom x) =
      bicomplexDiagonalDifferential K n (bicomplexToDiagonal K (n + 1) x) := by
  simp only [bicomplexDiagonalDifferential, LinearMap.comp_apply, bicomplexFromToDiagonal]

theorem bicomplexToDiagonal_d₁_succ (n i j : ℕ) (h : i + j = n)
    (x : (K.X (i + 1)).X j) :
    bicomplexToDiagonal K n ((K.d₁ (ComplexShape.down ℕ) (i + 1) j n).hom x) =
      Pi.single ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩
        (((K.d (i + 1) i).f j).hom x) := by
  have hd := K.d₁_eq (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)
    j n h
  simp only [show (ComplexShape.down ℕ).ε₁ (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) (i + 1, j) = 1 from rfl, one_smul] at hd
  rw [hd]
  change bicomplexToDiagonal K n
    ((K.ιTotal (ComplexShape.down ℕ) i j n h).hom (((K.d (i + 1) i).f j).hom x)) = _
  exact bicomplexToDiagonal_ι K n
    ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩ _

theorem bicomplexToDiagonal_d₁_zero (n j : ℕ) (x : (K.X 0).X j) :
    bicomplexToDiagonal K n ((K.d₁ (ComplexShape.down ℕ) 0 j n).hom x) = 0 := by
  rw [K.d₁_eq_zero (ComplexShape.down ℕ) 0 j n (by simp [ComplexShape.down])]
  simp

theorem bicomplexToDiagonal_d₂_succ (n i j : ℕ) (h : i + j = n)
    (x : (K.X i).X (j + 1)) :
    bicomplexToDiagonal K n ((K.d₂ (ComplexShape.down ℕ) i (j + 1) n).hom x) =
      (-1 : ℤˣ) ^ i • Pi.single
        ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩
        (((K.X i).d (j + 1) j).hom x) := by
  have hd := K.d₂_eq (ComplexShape.down ℕ) i
    (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl) n h
  rw [hd]
  change bicomplexToDiagonal K n
    ((-1 : ℤˣ) ^ i •
      (K.ιTotal (ComplexShape.down ℕ) i j n h).hom (((K.X i).d (j + 1) j).hom x)) = _
  simp only [Units.smul_def, map_zsmul]
  rw [bicomplexToDiagonal_ι K n
    ⟨(i, j), Finset.HasAntidiagonal.mem_antidiagonal.mpr h⟩]

theorem bicomplexToDiagonal_d₂_zero (n i : ℕ) (x : (K.X i).X 0) :
    bicomplexToDiagonal K n ((K.d₂ (ComplexShape.down ℕ) i 0 n).hom x) = 0 := by
  rw [K.d₂_eq_zero (ComplexShape.down ℕ) i 0 n (by simp [ComplexShape.down])]
  simp

theorem bicomplexDiagonalDifferential_single (n : ℕ)
    (p : ↥(Finset.HasAntidiagonal.antidiagonal (n + 1)))
    (x : (K.X p.1.1).X p.1.2) :
    bicomplexDiagonalDifferential K n (Pi.single p x) =
      bicomplexToDiagonal K n ((K.d₁ (ComplexShape.down ℕ) p.1.1 p.1.2 n).hom x) +
      bicomplexToDiagonal K n ((K.d₂ (ComplexShape.down ℕ) p.1.1 p.1.2 n).hom x) := by
  have h : K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 (n + 1)
      (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2) ≫
        (K.total (ComplexShape.down ℕ)).d (n + 1) n =
      K.d₁ (ComplexShape.down ℕ) p.1.1 p.1.2 n +
        K.d₂ (ComplexShape.down ℕ) p.1.1 p.1.2 n := by
    rw [HomologicalComplex₂.total_d, CategoryTheory.Preadditive.comp_add,
      K.ι_D₁, K.ι_D₂]
  simp only [bicomplexDiagonalDifferential, LinearMap.comp_apply,
    bicomplexFromDiagonal_single]
  rw [show ((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom
      ((K.ιTotal (ComplexShape.down ℕ) p.1.1 p.1.2 (n + 1)
        (Finset.HasAntidiagonal.mem_antidiagonal.mp p.2)).hom x) = _ from
      congrArg (fun f => f.hom x) h]
  exact map_add _ _ _

theorem bicomplexDiagonalDifferential_squared (n : ℕ)
    (x : bicomplexDiagonal K (n + 1 + 1)) :
    bicomplexDiagonalDifferential K n (bicomplexDiagonalDifferential K (n + 1) x) = 0 := by
  simp only [bicomplexDiagonalDifferential, LinearMap.comp_apply,
    bicomplexFromToDiagonal]
  have h := (K.total (ComplexShape.down ℕ)).d_comp_d (n + 1 + 1) (n + 1) n
  have hx := congrArg (fun f => f.hom (bicomplexFromDiagonal K (n + 1 + 1) x)) h
  change ((K.total (ComplexShape.down ℕ)).d (n + 1) n).hom
    (((K.total (ComplexShape.down ℕ)).d (n + 1 + 1) (n + 1)).hom
      (bicomplexFromDiagonal K (n + 1 + 1) x)) = 0 at hx
  rw [hx, map_zero]

end PolycyclicRecognition

end

end OAI
