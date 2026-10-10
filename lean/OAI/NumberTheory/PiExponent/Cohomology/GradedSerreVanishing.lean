import OAI.NumberTheory.PiExponent.Cohomology.GradedCechBound
import OAI.NumberTheory.PiExponent.Polynomials.GradedSerreStep

namespace OAI

namespace PiExponent.GradedSerreVanishing
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.GradedSerreStep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {J R : Type u} [Fintype J] [DecidableEq J] [CommRing R] [IsNoetherianRing R]

theorem eventually_hasPrimitive_aux (depth : ℕ) :
    ∀ {M σM : Type u} [AddCommGroup M] [Module (MvPolynomial J R) M]
      [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
      (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
      [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]
      (q : ℕ), Fintype.card J ≤ q + 1 + depth →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  induction depth with
  | zero =>
      intro M σM _ _ _ _ _ 𝓜 _ _ q hq
      refine ⟨0, ?_⟩
      intro n _ c hc
      exact GradedCechBound.primitives (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem
        n (by omega) c hc
  | succ depth ih =>
      intro M σM _ _ _ _ _ 𝓜 _ _ q hq
      obtain ⟨rank, w, g, hg, hsurj, N, hstep⟩ := exists_syzygy_eventual_step (J := J) (R := R) 𝓜
      let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
      let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
      let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
      obtain ⟨N₁, h₁⟩ := ih 𝓚 (q + 1) (by omega)
      refine ⟨max N N₁, ?_⟩
      intro n hn
      exact (hstep n ((le_max_left _ _).trans hn)).2 q
        (h₁ n ((le_max_right _ _).trans hn))

variable {M σM : Type u} [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

theorem eventually_hasPrimitive (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPrimitive (J := J) (R := R) 𝓜 n q :=
  eventually_hasPrimitive_aux (Fintype.card J) 𝓜 q (by omega)

theorem eventually_all_positive :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓜 n q := by
  classical
  have hq (q : Fin (Fintype.card J)) := eventually_hasPrimitive (J := J) (R := R) 𝓜 q.val
  choose N hN using hq
  refine ⟨∑ q, N q, ?_⟩
  intro n hn q c hc
  by_cases hbound : Fintype.card J ≤ q + 1
  · exact GradedCechBound.primitives (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem
      n hbound c hc
  · have hq' : q < Fintype.card J := by omega
    have hNq : N ⟨q, hq'⟩ ≤ ∑ q, N q :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.mem_univ (⟨q, hq'⟩ : Fin (Fintype.card J)))
    exact hN ⟨q, hq'⟩ n (hNq.trans hn) c hc

theorem eventually_augmentation_recovery :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasRecovery (J := J) (R := R) 𝓜 n := by
  obtain ⟨rank, w, g, hg, hsurj, N, hstep⟩ := exists_syzygy_eventual_step (J := J) (R := R) 𝓜
  let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
  let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
  let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
  obtain ⟨N₁, h₁⟩ := eventually_hasPrimitive (J := J) (R := R) 𝓚 0
  refine ⟨max N N₁, ?_⟩
  intro n hn
  exact (hstep n ((le_max_left _ _).trans hn)).1 (h₁ n ((le_max_right _ _).trans hn))

end
end PiExponent.GradedSerreVanishing

end OAI
