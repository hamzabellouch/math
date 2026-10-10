import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

namespace Invariant233

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem vonNeumannAlgebra_isClosed (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

variable {T : ℝ}

theorem fourier_mem_starSubalgebra_of_one
    (S : StarSubalgebra ℂ C(AddCircle T, ℂ))
    (h : fourier 1 ∈ S) (n : ℤ) : fourier n ∈ S := by
  have hzero : (fourier (T := T) 0) = 1 := by
    ext x
    exact fourier_zero
  have hneg : (fourier (T := T) (-1)) = star (fourier 1) := by
    ext x
    exact fourier_neg
  have hadd (a b : ℤ) : (fourier (T := T) (a + b)) = fourier a * fourier b := by
    ext x
    exact fourier_add
  induction n using Int.induction_on with
  | zero => rw [hzero]; exact S.one_mem
  | succ n hn =>
      rw [hadd]
      exact S.mul_mem hn h
  | pred n hn =>
      rw [sub_eq_add_neg, hadd, hneg]
      exact S.mul_mem hn (show star (fourier 1) ∈ S from star_mem h)

variable [Fact (0 < T)]

theorem mem_closed_starSubalgebra_of_fourier_one
    (S : StarSubalgebra ℂ C(AddCircle T, ℂ))
    (hS : IsClosed (S : Set C(AddCircle T, ℂ)))
    (h : fourier 1 ∈ S) (a : C(AddCircle T, ℂ)) : a ∈ S := by
  have hspan : Submodule.span ℂ (range (fourier (T := T))) ≤
      S.toSubalgebra.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact fourier_mem_starSubalgebra_of_one S h n
  have hdense := Submodule.topologicalClosure_minimal _ hspan hS
  rw [span_fourier_closure_eq_top] at hdense
  exact hdense (Submodule.mem_top)

theorem continuous_circle_representation_mem
    (Φ : C(AddCircle T, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (hΦ : Continuous Φ)
    (M : VonNeumannAlgebra H) (h : Φ (fourier 1) ∈ M)
    (a : C(AddCircle T, ℂ)) : Φ a ∈ M := by
  let S := StarSubalgebra.comap Φ M.toStarSubalgebra
  have hS : IsClosed (S : Set C(AddCircle T, ℂ)) :=
    (vonNeumannAlgebra_isClosed M).preimage hΦ
  exact mem_closed_starSubalgebra_of_fourier_one S hS h a

end Invariant233

end OAI
