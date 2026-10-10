import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel

namespace OAI
noncomputable section
namespace LittleFinitistic.TriangularExactness
universe u v
variable {R : Type u} [Ring R] {l : ℕ}
variable (E F G : Fin l → Type v)
variable [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

/-- A finite upper triangular differential with exact diagonal complexes is exact.
The argument eliminates one coordinate at a time; the modules may be arbitrary. -/
theorem exact_of_diagonal
    (d : (∀ i, E i) →ₗ[R] (∀ i, F i)) (e : (∀ i, F i) →ₗ[R] (∀ i, G i))
    (d₀ : ∀ i, E i →ₗ[R] F i) (e₀ : ∀ i, F i →ₗ[R] G i)
    (hzero : e.comp d = 0)
    (hd : ∀ (i : Fin l) (x : E i) (j : Fin l), j.val < i.val → d (Pi.single i x) j = 0)
    (hdi : ∀ (i : Fin l) (x : E i), d (Pi.single i x) i = d₀ i x)
    (he : ∀ (i : Fin l) (z : ∀ j, F j), (∀ j : Fin l, j.val < i.val → z j = 0) →
      e z i = e₀ i (z i))
    (hex : ∀ i, Function.Exact (d₀ i) (e₀ i)) : Function.Exact d e := by
  classical
  intro z
  constructor
  · intro hz
    have step (n : ℕ) (hn : n ≤ l) :
        ∃ w : ∀ i, E i, ∀ j : Fin l, j.val < n → (z-d w) j = 0 := by
      induction n with
      | zero => exact ⟨0,fun j hj => by omega⟩
      | succ n ih =>
        obtain ⟨w,hw⟩ := ih (by omega)
        let i : Fin l := ⟨n,by omega⟩
        have hclosed : e (z-d w) = 0 := by
          rw [map_sub,hz]
          have hed : e (d w) = 0 := congrArg (fun f : (∀ i, E i) →ₗ[R] (∀ i, G i) => f w) hzero
          rw [hed,sub_self]
        have hei : e₀ i ((z-d w) i) = 0 := by
          rw [← he i (z-d w) (fun j hj => hw j hj)]
          exact congrArg (fun x => x i) hclosed
        obtain ⟨y,hy⟩ := (hex i _).mp hei
        refine ⟨w + Pi.single i y, ?_⟩
        intro j hj
        by_cases hji : j.val < n
        · have hj0 := hd i y j hji
          change z j - d (w + Pi.single i y) j = 0
          rw [map_add,Pi.add_apply,hj0,add_zero]
          exact hw j hji
        · have hij : j = i := Fin.ext (by dsimp [i]; omega)
          subst j
          change z i - d (w + Pi.single i y) i = 0
          rw [map_add,Pi.add_apply,hdi,hy]
          change z i - (d w i + (z i - d w i)) = 0
          abel
    obtain ⟨w,hw⟩ := step l (by rfl)
    refine ⟨w, ?_⟩
    ext i
    exact (sub_eq_zero.mp (hw i i.isLt)).symm
  · rintro ⟨w,rfl⟩
    exact congrArg (fun f : (∀ i, E i) →ₗ[R] (∀ i, G i) => f w) hzero
end LittleFinitistic.TriangularExactness

end

end OAI
