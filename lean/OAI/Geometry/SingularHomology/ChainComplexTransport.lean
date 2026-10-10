import OAI.Geometry.SingularHomology.HomologyCycle

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

section ChainMaps

variable {R : Type} [Ring R]
variable {C D : ChainComplex (ModuleCat R) ℕ}
variable {A B : ℕ → ModuleCat R}

def chainMapOfLinearModels
    (e : ∀ n, A n ≃ₗ[R] C.X n) (f : ∀ n, B n ≃ₗ[R] D.X n)
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (he : ∀ n x, (C.d (n + 1) n).hom (e (n + 1) x) = e n (dA n x))
    (hf : ∀ n x, (D.d (n + 1) n).hom (f (n + 1) x) = f n (dB n x))
    (T : ∀ n, A n →ₗ[R] B n)
    (hT : ∀ n x, dB n (T (n + 1) x) = T n (dA n x)) : C ⟶ D where
  f n := ModuleCat.ofHom ((f n).toLinearMap.comp ((T n).comp (e n).symm.toLinearMap))
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (e (j + 1)).surjective x
    change (D.d (j + 1) j).hom
      (f (j + 1) (T (j + 1) ((e (j + 1)).symm (e (j + 1) y)))) =
      f j (T j ((e j).symm ((C.d (j + 1) j).hom (e (j + 1) y))))
    simp only [LinearEquiv.symm_apply_apply, hf, he, hT]

@[simp]
theorem chainMapOfLinearModels_apply
    (e : ∀ n, A n ≃ₗ[R] C.X n) (f : ∀ n, B n ≃ₗ[R] D.X n)
    (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
    (he : ∀ n x, (C.d (n + 1) n).hom (e (n + 1) x) = e n (dA n x))
    (hf : ∀ n x, (D.d (n + 1) n).hom (f (n + 1) x) = f n (dB n x))
    (T : ∀ n, A n →ₗ[R] B n)
    (hT : ∀ n x, dB n (T (n + 1) x) = T n (dA n x))
    (n : ℕ) (x : A n) :
    ((chainMapOfLinearModels e f dA dB he hf T hT).f n).hom (e n x) = f n (T n x) := by
  simp [chainMapOfLinearModels]

end ChainMaps

section Homotopies

variable {V : Type*} [Category V] [Preadditive V]
variable {C D : ChainComplex V ℕ} (f g : C ⟶ D)

def chainHomotopyMatrix (h : ∀ n, C.X n ⟶ D.X (n + 1)) (i j : ℕ) : C.X i ⟶ D.X j :=
  if hij : i + 1 = j then h i ≫ eqToHom (congrArg D.X hij) else 0

@[simp]
theorem chainHomotopyMatrix_succ (h : ∀ n, C.X n ⟶ D.X (n + 1)) (i : ℕ) :
    chainHomotopyMatrix h i (i + 1) = h i := by
  simp [chainHomotopyMatrix]

def chainHomotopyOfComponents (h : ∀ n, C.X n ⟶ D.X (n + 1))
    (hzero : f.f 0 = h 0 ≫ D.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n + 1) =
      C.d (n + 1) n ≫ h n + h (n + 1) ≫ D.d (n + 2) (n + 1) + g.f (n + 1)) :
    Homotopy f g where
  hom := chainHomotopyMatrix h
  zero i j hij := by
    change ¬ i + 1 = j at hij
    simp [chainHomotopyMatrix, hij]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simpa using hzero
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simpa using hsucc n

end Homotopies

section LinearHomotopies

variable {R : Type} [Ring R]
variable {C D : ChainComplex (ModuleCat R) ℕ}
variable {A B : ℕ → ModuleCat R}
variable (e : ∀ n, A n ≃ₗ[R] C.X n) (f : ∀ n, B n ≃ₗ[R] D.X n)
variable (dA : ∀ n, A (n + 1) →ₗ[R] A n) (dB : ∀ n, B (n + 1) →ₗ[R] B n)
variable (he : ∀ n x, (C.d (n + 1) n).hom (e (n + 1) x) = e n (dA n x))
variable (hf : ∀ n x, (D.d (n + 1) n).hom (f (n + 1) x) = f n (dB n x))
variable (S T : ∀ n, A n →ₗ[R] B n)
variable (hS : ∀ n x, dB n (S (n + 1) x) = S n (dA n x))
variable (hT : ∀ n x, dB n (T (n + 1) x) = T n (dA n x))

def chainHomotopyOfLinearModels
    (H : ∀ n, A n →ₗ[R] B (n + 1))
    (hzero : ∀ x, S 0 x = dB 0 (H 0 x) + T 0 x)
    (hsucc : ∀ n x, S (n + 1) x =
      H n (dA n x) + dB (n + 1) (H (n + 1) x) + T (n + 1) x) :
    Homotopy (chainMapOfLinearModels e f dA dB he hf S hS)
      (chainMapOfLinearModels e f dA dB he hf T hT) := by
  let h : ∀ n, C.X n ⟶ D.X (n + 1) := fun n =>
    ModuleCat.ofHom ((f (n + 1)).toLinearMap.comp
      ((H n).comp (e n).symm.toLinearMap))
  apply chainHomotopyOfComponents _ _ h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (e 0).surjective x
    simp [chainMapOfLinearModels, h, hf, hzero, map_add]
  · intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (e (n + 1)).surjective x
    simp [chainMapOfLinearModels, h, he, hf, hsucc, map_add]

theorem homologyMap_eq_of_linearModel_homotopy
    (H : ∀ n, A n →ₗ[R] B (n + 1))
    (hzero : ∀ x, S 0 x = dB 0 (H 0 x) + T 0 x)
    (hsucc : ∀ n x, S (n + 1) x =
      H n (dA n x) + dB (n + 1) (H (n + 1) x) + T (n + 1) x)
    (n : ℕ) :
    HomologicalComplex.homologyMap (chainMapOfLinearModels e f dA dB he hf S hS) n =
      HomologicalComplex.homologyMap (chainMapOfLinearModels e f dA dB he hf T hT) n :=
  (chainHomotopyOfLinearModels e f dA dB he hf S T hS hT H hzero hsucc).homologyMap_eq n

end LinearHomotopies

end Problem340

end

end OAI
