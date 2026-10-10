import OAI.NumberTheory.PiExponent.Ampleness.ReesPushdown
import OAI.NumberTheory.PiExponent.Polynomials.GradedSerre

namespace OAI

namespace PiExponent.ReesPolynomialPresentation
noncomputable section
open scoped BigOperators
open Polynomial PiExponentSeshadri.ReesGrading
variable {R J : Type*} [CommRing R] (I : Ideal R) (a : J → I)

def presentation : MvPolynomial J R →ₐ[R] reesAlgebra I :=
  MvPolynomial.aeval (fun j => generator I (a j))

@[simp] theorem presentation_X (j : J) : presentation I a (MvPolynomial.X j) = generator I (a j) :=
  MvPolynomial.aeval_X _ _

theorem presentation_monomial_mem (b : J →₀ ℕ) (r : R) :
    presentation I a (MvPolynomial.monomial b r) ∈ piece I b.degree := by
  classical
  rw [presentation, MvPolynomial.aeval_monomial]
  have hp : (∏ j ∈ b.support, generator I (a j) ^ b j) ∈ piece I b.degree := by
    have h := SetLike.prod_mem_graded (piece I) (fun j => b j)
      (fun j => generator I (a j) ^ b j) (F := b.support)
      (fun j _ => by simpa using SetLike.pow_mem_graded (b j) (generator_mem I (a j)))
    change (∏ j ∈ b.support, generator I (a j) ^ b j) ∈ piece I (∑ j ∈ b.support, b j)
    exact h
  have hr : algebraMap R (reesAlgebra I) r ∈ piece I 0 := by
    simp [mem_piece]
  simpa only [zero_add, Finsupp.prod] using SetLike.mul_mem_graded hr hp

theorem presentation_homogeneous_mem {n : ℕ} {p : MvPolynomial J R}
    (hp : p.IsHomogeneous n) : presentation I a p ∈ piece I n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (piece I n).zero_mem
  | add p q hp hq ihp ihq => simpa only [map_add] using (piece I n).add_mem ihp ihq
  | monomial b r hb =>
      have hb' : b.degree = n := by rw [Finsupp.degree_eq_weight_one, ← Pi.one_def, hb]
      simpa only [hb'] using presentation_monomial_mem I a b r

theorem evaluation_presentation (p : MvPolynomial J R) :
    evaluation I (presentation I a p) = MvPolynomial.eval (fun j => (a j).val) p := by
  have h : (evaluation I).comp (presentation I a).toRingHom =
      (MvPolynomial.eval₂Hom (RingHom.id R) (fun j => (a j).val)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [presentation, evaluation]
    · intro j
      simp [presentation, evaluation_generator]
  exact DFunLike.congr_fun h p

theorem homogeneous_piece_surjective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (z : piece I n) :
    ∃ p : MvPolynomial J R, p.IsHomogeneous n ∧ presentation I a p = z.val := by
  have hz : (((z.val : reesAlgebra I) : R[X]).coeff n) ∈
      (Ideal.span (Set.range fun j => (a j).val)) ^ n := by
    rw [ha]
    exact z.val.property n
  obtain ⟨p, hp, heval⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous
    (fun j => (a j).val) _).mp hz
  refine ⟨p, hp, ?_⟩
  have hmem := presentation_homogeneous_mem I a hp
  apply Subtype.ext
  rw [(mem_piece I n _).mp hmem, (mem_piece I n _).mp z.property]
  congr 1
  have h := evaluation_presentation I a p
  rw [evaluation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] at h
  change Polynomial.eval 1 ((presentation I a p : reesAlgebra I) : R[X]) = _ at h
  rw [(mem_piece I n _).mp hmem] at h
  simpa only [Polynomial.eval_monomial, one_pow, mul_one] using h.trans heval

theorem presentation_surjective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    Function.Surjective (presentation I a) := by
  classical
  intro z
  have hn (n : ℕ) := homogeneous_piece_surjective I a ha n (component I n z)
  choose p hp hpres using hn
  refine ⟨∑ n ∈ ((z : reesAlgebra I) : R[X]).support, p n, ?_⟩
  rw [map_sum]
  simp_rw [hpres]
  apply Subtype.ext
  change (reesAlgebra I).val (∑ n ∈ ((z : reesAlgebra I) : R[X]).support,
    (component I n z).val) = (z : R[X])
  rw [map_sum]
  exact ((z : R[X]).as_sum_support).symm

@[instance_reducible]
def presentationAlgebra : Algebra (MvPolynomial J R) (reesAlgebra I) :=
  (presentation I a).toRingHom.toAlgebra

theorem finite_presented_module
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    Module.Finite (MvPolynomial J R) (reesAlgebra I) := by
  let := presentationAlgebra I a
  exact Module.Finite.of_surjective
    (Algebra.linearMap (MvPolynomial J R) (reesAlgebra I)) (presentation_surjective I a ha)

theorem exists_finite_presentation [IsNoetherianRing R] :
    ∃ (s : Finset R) (a : s → I),
      (∀ j : s, (a j).val = j.val) ∧
      Ideal.span (Set.range fun j => (a j).val) = I ∧
      Function.Surjective (presentation I a) ∧
      ∀ n (z : piece I n), ∃ p : MvPolynomial s R,
        p.IsHomogeneous n ∧ presentation I a p = z.val := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  let a : s → I := fun j => ⟨j.val, by
    rw [← hs]
    exact Submodule.subset_span j.property⟩
  have ha : Ideal.span (Set.range fun j => (a j).val) = I := by
    simpa only [a, Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
  exact ⟨s, a, fun _ => rfl, ha, presentation_surjective I a ha,
    homogeneous_piece_surjective I a ha⟩

end
end PiExponent.ReesPolynomialPresentation

end OAI
