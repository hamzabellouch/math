import OAI.Analysis.Laughlin.Fock.EigenvalueGap
import OAI.Analysis.Laughlin.Operators.SpectralKernelDistance

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators InnerProductSpace

noncomputable def occupationEuclidean (Q : ℕ) :
    Space Q ≃ₗ[ℂ] EuclideanSpace ℂ (Finset (Fin (Q+1))) :=
  (occupationBasis Q).equivFun.trans (WithLp.linearEquiv 2 ℂ (Finset (Fin (Q+1)) → ℂ)).symm

theorem occupationEuclidean_inner (Q : ℕ) (x y : Space Q) :
    inner ℂ (occupationEuclidean Q x) (occupationEuclidean Q y) = occupationInner Q x y := by
  simp only [occupationEuclidean,LinearEquiv.trans_apply,PiLp.inner_apply,
    Module.Basis.equivFun_apply,occupationInner]
  apply Finset.sum_congr rfl
  intro A hA
  change (occupationBasis Q).repr y A * star ((occupationBasis Q).repr x A) = _
  ring

theorem occupationEuclidean_norm (Q : ℕ) (x : Space Q) :
    ‖occupationEuclidean Q x‖^2 = occupationNormSq Q x := by
  have h := occupationEuclidean_inner Q x x
  rw [inner_self_eq_norm_sq_to_K,occupationInner_self] at h
  change (‖occupationEuclidean Q x‖ : ℂ)^2 = (occupationNormSq Q x : ℂ) at h
  exact_mod_cast h

noncomputable def euclideanFockHamiltonian (Q : ℕ) :
    Module.End ℂ (EuclideanSpace ℂ (Finset (Fin (Q+1)))) :=
  (occupationEuclidean Q).toLinearMap.comp
    ((sourceFockHamiltonian Q).comp (occupationEuclidean Q).symm.toLinearMap)

theorem euclideanFockHamiltonian_apply (Q : ℕ) (x : Space Q) :
    euclideanFockHamiltonian Q (occupationEuclidean Q x) =
      occupationEuclidean Q (sourceFockHamiltonian Q x) := by
  simp [euclideanFockHamiltonian]

theorem euclideanFockHamiltonian_symmetric (Q : ℕ) :
    (euclideanFockHamiltonian Q).IsSymmetric := by
  intro x y
  obtain ⟨u,rfl⟩ := (occupationEuclidean Q).surjective x
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective y
  simp only [euclideanFockHamiltonian_apply,occupationEuclidean_inner]
  exact sourceFockHamiltonian_symmetric Q u v

theorem physical_fock_kernel_distance_uniform :
    ∃ Q₀ : ℕ, 25 ≤ Q₀ ∧ ∀ Q : ℕ, Q₀ ≤ Q → ∀ x : Space Q,
      ∃ y : Space Q, sourceFockHamiltonian Q y=0 ∧
        (1/100 : ℝ)*occupationNormSq Q (x-y) ≤ sourceFockEnergy Q x := by
  obtain ⟨Q₀,h25,hgap⟩ := physical_fock_eigenvalue_gap_uniform
  refine ⟨Q₀,h25,fun Q hQ x => ?_⟩
  have hg : ∀ v : EuclideanSpace ℂ (Finset (Fin (Q+1))), v≠0 → ∀ a : ℝ,
      euclideanFockHamiltonian Q v=(a : ℂ) • v → a=0 ∨ (1/100 : ℝ)≤a := by
    intro v hv a he
    obtain ⟨u,rfl⟩ := (occupationEuclidean Q).surjective v
    apply hgap Q hQ u (by intro hu; simp [hu] at hv) a
    apply (occupationEuclidean Q).injective
    simpa only [euclideanFockHamiltonian_apply,map_smul] using he
  obtain ⟨z,hz,hb⟩ := spectral_kernel_distance (euclideanFockHamiltonian Q)
    (euclideanFockHamiltonian_symmetric Q) (1/100) (by norm_num) hg (occupationEuclidean Q x)
  obtain ⟨y,rfl⟩ := (occupationEuclidean Q).surjective z
  refine ⟨y,?_,?_⟩
  · apply (occupationEuclidean Q).injective
    simpa only [euclideanFockHamiltonian_apply,map_zero] using hz
  · rw [← map_sub,occupationEuclidean_norm,euclideanFockHamiltonian_apply,
      occupationEuclidean_inner,sourceFockHamiltonian_quadratic,Complex.ofReal_re] at hb
    exact hb

end Laughlin.Fock

end OAI
