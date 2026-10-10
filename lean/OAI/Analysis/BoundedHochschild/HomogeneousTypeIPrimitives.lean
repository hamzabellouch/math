import OAI.Analysis.BoundedHochschild.MatrixBlockGroups

namespace OAI

/-!
# Norm-one primitives on finite homogeneous type I algebras

Finite central partitions and signed permutation groups give exact homotopies
on central projection multiples of matrix entries. Their bounded weak-star
limit is exact everywhere by the projection-span theorem in the commutant.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildMatrixSystems HochschildSakai

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem finite_homogeneous_typeI_primitive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {d : ℕ} (E : MatrixSystem M d) (hcomm : ∀ a b : E.commutant, Commute a b)
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  classical
  let : CommCStarAlgebra E.commutant := { mul_comm := fun a b => (hcomm a b).eq }
  obtain ⟨P, _, hP⟩ := exists_abstract_star_preadjoint e
  let eC := E.commutantPredualEquiv e (mul_hasPreadjoint e)
    (mul_right_hasPreadjoint e) P hP
  let Q := {q : E.commutant // IsStarProjection q}
  choose r p hp ho hs href using fun S : Finset Q => exists_refining_partition S
  let := Fintype.ofFinite E.signedPermutationGroup
  let F (S : Finset Q) : Cochain M n := finiteUnitaryHomotopy
    (E.matrixBlockHom hcomm (p S) (hp S) (ho S) (hs S)) f
  have hFn (S : Finset Q) : ‖F S‖ ≤ ‖f‖ := finiteUnitaryHomotopy_norm _ f
  let U : Ultrafilter (Finset Q) := Ultrafilter.of atTop
  have hU : (U : Filter (Finset Q)) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨g, hgn, ht⟩ := bounded_cochain_ultralimit e U F ‖f‖ (norm_nonneg _) hFn
  have hproj (q : Q) (a b : Fin d) (x : Fin n → M) :
      differentialValue g (Fin.cons ((q.val : M) * E.entry a b) x) =
        f (Fin.cons ((q.val : M) * E.entry a b) x) := by
    have he : (fun S => differentialValue (F S)
        (Fin.cons ((q.val : M) * E.entry a b) x)) =ᶠ[U]
        (fun _ => f (Fin.cons ((q.val : M) * E.entry a b) x)) := by
      apply hU
      filter_upwards [eventually_ge_atTop ({q} : Finset Q)] with S hS
      exact finiteUnitaryHomotopy_exact_span _ f hf
        (E.matrixBlock_refined_entry_mem_span hcomm (p S) (hp S) (ho S) (hs S) q.val
          (href S q (hS (Finset.mem_singleton_self q))) a b) x
    apply predual_tendsto_unique e (predual_tendsto_differential_of_predual e ht _)
    intro z
    exact tendsto_const_nhds.congr' (he.mono fun _ h =>
      congrArg (fun a : M => e.symm a z) h.symm)
  refine ⟨g, hgn, fun x => ?_⟩
  let L := firstSliceN (differential g - f) (Fin.tail x)
  have hcoord (a b : Fin d) (c : E.commutant) : L ((c : M) * E.entry a b) = 0 := by
    let T : E.commutant →L[ℂ] M := L.comp
      (((ContinuousLinearMap.mul ℂ M).flip (E.entry a b)).comp
        E.commutant.toSubalgebra.toSubmodule.subtypeL)
    have hspan : Submodule.span ℂ {q : E.commutant | IsStarProjection q} ≤ T.ker := by
      apply Submodule.span_le.mpr
      intro q hq
      change L ((q : M) * E.entry a b) = 0
      simpa only [L, firstSliceN_apply, sub_apply, differential_apply] using
        sub_eq_zero.mpr (hproj ⟨q, hq⟩ a b (Fin.tail x))
    have hclosed := Submodule.topologicalClosure_minimal _ hspan T.isClosed_ker
    rw [projection_span_dense eC] at hclosed
    exact hclosed (Submodule.mem_top : c ∈ (⊤ : Submodule ℂ E.commutant))
  have hzero : L (x 0) = 0 := by
    rw [← E.reconstruct (x 0), map_sum]
    apply Finset.sum_eq_zero
    intro a _
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    have h := hcoord a b ⟨_, E.coefficient_mem a b (x 0)⟩
    simpa only [(E.coefficient_mem a b (x 0) a b).eq] using h
  apply sub_eq_zero.mp
  simpa only [L, firstSliceN_apply, sub_apply, differential_apply, Fin.cons_self_tail] using hzero

/-- An abelian diagonal corner is the concrete homogeneous type I hypothesis. -/
theorem finite_homogeneous_typeI_primitive_of_abelian_diagonal
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {d : ℕ} (E : MatrixSystem M d) (i : Fin d)
    (hi : FinitePathMain.AbelianProjection (E.entry i i))
    {n : ℕ} (f : Cochain M (n + 1)) (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x :=
  finite_homogeneous_typeI_primitive e E (E.commutant_commutative_of_abelian_diagonal i hi) f hf

end KadisonRingrose
end BoundedHochschild

end

end OAI
