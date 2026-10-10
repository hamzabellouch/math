import OAI.Algebra.Finitistic.Ordinary.OrdinaryTriangularExactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.FiniteColumnComplex
universe u
variable {R : Type u} [Ring R] {l : ℕ}
variable (K : Fin l → CochainComplex (ModuleCat.{u} R) ℤ)

abbrev term (n : ℤ) := ∀ i, (K i).X n

/-- A finite-column total differential, recorded independently of a chosen direct-sum presentation. -/
structure Differential where
  d : ∀ n : ℤ, term K n →ₗ[R] term K (n+1)
  square : ∀ n, (d (n+1)).comp (d n) = 0
  triangular : ∀ (n : ℤ) (i : Fin l) (z : term K n),
    (∀ j : Fin l, j.val < i.val → z j = 0) →
    d n z i = ((K i).d n (n+1)).hom (z i)

variable (δ : Differential K)

def complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of R (term K n))
    (fun n => ModuleCat.ofHom (δ.d n)) (fun n => ModuleCat.hom_ext (δ.square n))

@[simp] theorem complex_d (n : ℤ) :
    (complex K δ).d n (n+1) = ModuleCat.ofHom (δ.d n) := by
  exact CochainComplex.of_d (fun n => ModuleCat.of R (term K n))
    (fun n => ModuleCat.ofHom (δ.d n)) n

@[simp] theorem complex_d_hom (n : ℤ) :
    ((complex K δ).d n (n+1)).hom = δ.d n := by
  rw [complex_d]
  rfl

theorem lower_single (n : ℤ) (i : Fin l) (x : (K i).X n) (j : Fin l) (hji : j.val < i.val) :
    δ.d n (Pi.single i x : term K n) j = 0 := by
  classical
  have ht : ∀ t : Fin l, t.val < j.val → (Pi.single i x : term K n) t = 0 := by
    intro t ht
    simp [show t ≠ i from by intro h; subst t; omega]
  rw [δ.triangular n j (Pi.single i x) ht]
  rw [Pi.single_eq_of_ne (show j ≠ i from by intro h; subst j; omega),map_zero]

theorem diagonal_single (n : ℤ) (i : Fin l) (x : (K i).X n) :
    δ.d n (Pi.single i x) i = ((K i).d n (n+1)).hom x := by
  classical
  have ht : ∀ j : Fin l, j.val < i.val → (Pi.single i x : term K n) j = 0 := by
    intro j hj
    simp [show j ≠ i from by intro h; subst j; omega]
  rw [δ.triangular n i (Pi.single i x) ht,Pi.single_eq_same]

/-- Finite totalization preserves acyclicity when every column is acyclic. -/
theorem acyclic (hK : ∀ i, (K i).Acyclic) : (complex K δ).Acyclic := by
  intro n
  have hn : n-1+1=n := by omega
  suffices hh : (complex K δ).ExactAt (n-1+1) by simpa only [hn] using hh
  apply (HomologicalComplex.exactAt_iff' _ (n-1) (n-1+1) ((n-1+1)+1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  have hex (i : Fin l) : Function.Exact
      ((K i).d (n-1) (n-1+1)).hom ((K i).d (n-1+1) ((n-1+1)+1)).hom := by
    have hh := (HomologicalComplex.exactAt_iff' (K i) (n-1) (n-1+1) ((n-1+1)+1)
      (by simp) (by simp)).mp (hK i _)
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hh
  have ht := TriangularExactness.exact_of_diagonal
    (fun i => (K i).X (n-1)) (fun i => (K i).X (n-1+1)) (fun i => (K i).X ((n-1+1)+1))
    (δ.d (n-1)) (δ.d (n-1+1))
    (fun i => ((K i).d (n-1) (n-1+1)).hom)
    (fun i => ((K i).d (n-1+1) ((n-1+1)+1)).hom)
    (δ.square (n-1)) (lower_single K δ (n-1)) (diagonal_single K δ (n-1))
    (δ.triangular (n-1+1)) hex
  change ∀ (z : term K (n-1+1)),
    ((complex K δ).d (n-1+1) ((n-1+1)+1)).hom z = 0 →
    ∃ w : term K (n-1), ((complex K δ).d (n-1) (n-1+1)).hom w = z
  simp only [complex_d_hom]
  exact fun z hz => (ht z).mp hz
end LittleFinitistic.FiniteColumnComplex

end

end OAI
