import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic

namespace OAI

noncomputable section
open Set

namespace Invariant233.ContinuousCircleImage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_natCast (n : ℕ) :
    (fourier (n : ℤ) : C(AddCircle (1 : ℝ), ℂ)) = fourier 1 ^ n := by
  induction n with
  | zero =>
    ext x
    simp only [Nat.cast_zero, pow_zero, ContinuousMap.one_apply]
    exact fourier_zero
  | succ n ih =>
    ext x
    rw [Nat.cast_succ]
    change fourier ((n : ℤ) + 1) x = (fourier 1 ^ (n + 1)) x
    rw [fourier_add, pow_succ, ContinuousMap.mul_apply, ← ih]

theorem isClosed_vonNeumannAlgebra (M : VonNeumannAlgebra H) :
    IsClosed (M : Set (H →L[ℂ] H)) := by
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

theorem image_mem
    (Φ : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (hΦ : Continuous Φ)
    (M : VonNeumannAlgebra H) (hV : Φ (fourier 1) ∈ M)
    (f : C(AddCircle (1 : ℝ), ℂ)) : Φ f ∈ M := by
  have hNat : ∀ n : ℕ, Φ (fourier (n : ℤ)) ∈ M := by
    intro n
    rw [fourier_natCast, map_pow]
    exact pow_mem hV n
  have hFourier : ∀ n : ℤ, Φ (fourier n) ∈ M := by
    intro n
    cases n with
    | ofNat n => exact hNat n
    | negSucc n =>
      have heq : (fourier (Int.negSucc n) : C(AddCircle (1 : ℝ), ℂ)) =
          star (fourier ((n + 1 : ℕ) : ℤ)) := by
        ext x
        change fourier (-((n + 1 : ℕ) : ℤ)) x = star (fourier ((n + 1 : ℕ) : ℤ) x)
        exact fourier_neg
      rw [heq, map_star]
      exact star_mem (hNat (n + 1))
  let K : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
    M.toStarSubalgebra.toSubalgebra.toSubmodule.comap Φ.toAlgHom.toLinearMap
  have hK : IsClosed (K : Set C(AddCircle (1 : ℝ), ℂ)) :=
    (isClosed_vonNeumannAlgebra M).preimage hΦ
  have hspan : Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hFourier n
  have hclosure := (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure_minimal hspan hK
  rw [span_fourier_closure_eq_top] at hclosure
  exact hclosure (Submodule.mem_top : f ∈ (⊤ : Submodule ℂ C(AddCircle (1 : ℝ), ℂ)))

theorem hom_ext_character
    (Φ Ψ : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hV : Φ (fourier 1) = Ψ (fourier 1)) : Φ = Ψ := by
  have hNat : ∀ n : ℕ, Φ (fourier (n : ℤ)) = Ψ (fourier (n : ℤ)) := by
    intro n
    rw [fourier_natCast, map_pow, map_pow, hV]
  have hFourier : ∀ n : ℤ, Φ (fourier n) = Ψ (fourier n) := by
    intro n
    cases n with
    | ofNat n => exact hNat n
    | negSucc n =>
      have heq : (fourier (Int.negSucc n) : C(AddCircle (1 : ℝ), ℂ)) =
          star (fourier ((n + 1 : ℕ) : ℤ)) := by
        ext x
        change fourier (-((n + 1 : ℕ) : ℤ)) x = star (fourier ((n + 1 : ℕ) : ℤ) x)
        exact fourier_neg
      rw [heq, map_star, map_star, hNat]
  let LΦ : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] (H →L[ℂ] H) :=
    ⟨Φ.toAlgHom.toLinearMap, hΦ⟩
  let LΨ : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] (H →L[ℂ] H) :=
    ⟨Ψ.toAlgHom.toLinearMap, hΨ⟩
  have hL : LΦ = LΨ := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top)
    rintro _ ⟨n, rfl⟩
    exact hFourier n
  apply DFunLike.ext
  intro a
  exact congrArg (fun L : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] (H →L[ℂ] H) => L a) hL

end Invariant233.ContinuousCircleImage

end

end OAI
