import OAI.Analysis.FactorGeneration.SpectralApproximation

namespace OAI

/-! # Testing commutation on the projections of a von Neumann algebra

Finite spectral sums approximate every self-adjoint element in norm.
Their commutation identities pass to the limit, and real/imaginary
decomposition gives the identity on the whole algebra.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commutes_vonNeumann_of_projections (N : VonNeumannAlgebra H)
    (C : H →L[ℂ] H) (hp : ∀ p : AlgebraProjection N, Commute C p.val.val) :
    ∀ a : N.toStarSubalgebra, Commute C a.val := by
  let K : Set N.toStarSubalgebra := {a | Commute C a.val}
  have hclosed : IsClosed K := isClosed_eq
    (continuous_const.mul continuous_subtype_val) (continuous_subtype_val.mul continuous_const)
  have hself (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) : a ∈ K := by
    rw [← hclosed.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨Q, c, _, hclose⟩ := exists_finite_spectral_approximation
      (identityProjection N) a ha ε hε
    let b : N.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
    have hbval : b.val = ∑ i, (c i : ℂ) • (Q.piece i).val.val := by
      change N.toStarSubalgebra.subtype (∑ i, (c i : ℂ) • (Q.piece i).val) = _
      rw [map_sum]
      simp only [map_smul]
      rfl
    refine ⟨b, ?_, ?_⟩
    · change C * b.val = b.val * C
      simp only [hbval,
        Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => (c i : ℂ) • z) (hp (Q.piece i)).eq)
    · simpa only [dist_eq_norm, identityProjection, one_mul, mul_one, b] using hclose
  intro a
  have hr := hself (ℜ a) (ℜ a).property
  have hi := hself (ℑ a) (ℑ a).property
  have he : a.val = (ℜ a : N.toStarSubalgebra).val +
      Complex.I • (ℑ a : N.toStarSubalgebra).val :=
    congrArg Subtype.val (realPart_add_I_smul_imaginaryPart a).symm
  change C * a.val = a.val * C
  change C * (ℜ a : N.toStarSubalgebra).val = (ℜ a : N.toStarSubalgebra).val * C at hr
  change C * (ℑ a : N.toStarSubalgebra).val = (ℑ a : N.toStarSubalgebra).val * C at hi
  rw [he, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hr, hi]

theorem mem_commutant_of_commutes_projections (N : VonNeumannAlgebra H)
    (C : H →L[ℂ] H) (hp : ∀ p : AlgebraProjection N, Commute C p.val.val) :
    C ∈ N.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact (commutes_vonNeumann_of_projections N C hp ⟨a, ha⟩).eq.symm

end

end KadisonKastler

end OAI
