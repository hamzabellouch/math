import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import OAI.AlgebraicGeometry.PlaneCurves.BinaryForms

namespace OAI

/-!
# Finite-dimensional cubic relations among section products
-/

section

noncomputable section
namespace Nagata.W02

/-- More vectors than the dimension yield an actual nonzero finitely supported
coefficient vector annihilated by their linear-combination map. -/
theorem exists_nonzero_linearRelation {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype I]
    (v : I → V) (hdim : Module.finrank K V < Fintype.card I) :
    ∃ c : I →₀ K, c ≠ 0 ∧ Finsupp.linearCombination K v c = 0 := by
  have hdep : ¬ LinearIndependent K v := by
    intro h
    exact (not_le_of_gt hdim) h.fintype_card_le_finrank
  obtain ⟨c, hc, hne⟩ := not_linearIndependent_iff_linearCombination.mp hdep
  exact ⟨c, hne, hc⟩

/-- Ten actual vectors in any space of dimension at most nine satisfy a
nontrivial coefficient relation. Repeated vectors and the zero vector are allowed. -/
theorem ten_vectors_relation {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (v : Fin 10 → V)
    (hdim : Module.finrank K V ≤ 9) :
    ∃ c : Fin 10 →₀ K, c ≠ 0 ∧ Finsupp.linearCombination K v c = 0 := by
  apply exists_nonzero_linearRelation v
  simpa only [Fintype.card_fin] using (lt_of_le_of_lt hdim (by decide : 9 < 10))

end Nagata.W02

end
end

section

noncomputable section
namespace Nagata.W02

theorem cubicExponent_sum (e : DegreeExponent 3) : ∑ i, e.val i = 3 := by
  simpa only [← Finsupp.degree_eq_sum] using e.property

theorem aeval_cubicMonomial_function {K X : Type*} [Field K]
    (s : Fin 3 → X → K) (e : DegreeExponent 3) :
    MvPolynomial.aeval s (MvPolynomial.monomial e.val (1 : K)) =
      fun z => ∏ i, s i z ^ e.val i := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  rw [Finsupp.prod_pow]
  funext z
  simp

end Nagata.W02

end
end

section

/-! A genuine nonzero homogeneous cubic relation from the dimension of the
actual span of its ten evaluated monomials. The automorphic degree-nine
section-space dimension and product membership are explicit inputs. -/
noncomputable section
namespace Nagata.W02

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The actual homogeneous degree-three exponent space has ten monomials. -/
theorem card_cubicExponent : Fintype.card (DegreeExponent 3) = 10 := by
  rw [card_degreeExponent]
  decide

/-- Ten actual cubic monomials in a subspace of dimension at most nine give a
nonzero genuine homogeneous cubic vanishing on the three algebra elements.
This theorem does not assert smoothness, irreducibility, or image equality. -/
theorem exists_nonzero_homogeneousCubic_relation (s : Fin 3 → A)
    (W : Submodule K A) [Module.Finite K W]
    (hdim : Module.finrank K W ≤ 9)
    (hmon : ∀ e : DegreeExponent 3,
      MvPolynomial.aeval s (MvPolynomial.monomial e.val (1 : K)) ∈ W) :
    ∃ P : MvPolynomial (Fin 3) K,
      P ≠ 0 ∧ P.IsHomogeneous 3 ∧ MvPolynomial.aeval s P = 0 := by
  let v : DegreeExponent 3 → W := fun e => ⟨_, hmon e⟩
  have hd : Module.finrank K W < Fintype.card (DegreeExponent 3) := by
    rw [card_cubicExponent]
    omega
  obtain ⟨c, hcne, hc⟩ := exists_nonzero_linearRelation v hd
  let F := (homogeneousCoefficientEquiv K 3).symm c
  have hFne : F ≠ 0 := by
    intro hz
    apply hcne
    have h := congrArg (homogeneousCoefficientEquiv K 3) hz
    simpa only [F, LinearEquiv.apply_symm_apply, map_zero] using h
  refine ⟨F.val, ?_, F.property, ?_⟩
  · intro hz
    exact hFne (Subtype.ext hz)
  · change MvPolynomial.aeval s
      (((homogeneousCoefficientEquiv K 3).symm c) : MvPolynomial (Fin 3) K) = 0
    rw [aeval_homogeneousCoefficientEquiv_symm]
    have hambient := congrArg (fun x : W => (x : A)) hc
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
      Submodule.coe_smul, Submodule.coe_zero, v] using hambient

end Nagata.W02

end
end

end OAI
