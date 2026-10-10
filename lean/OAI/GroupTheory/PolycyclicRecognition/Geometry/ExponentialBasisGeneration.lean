import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalExponentialOpen
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-! # Generation by exponential basis directions

The product of the basis one-parameter subgroups has invertible derivative
at the identity. A subgroup containing those curves is open, hence is the
whole connected group. No global exponential-chart assumption is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G] in
theorem exponentialProduct_mem_subgroup
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} {n : ℕ}
    (S : Subgroup G) (v : Fin n → E)
    (hv : ∀ i (t : ℝ), Exp (t • v i) ∈ S) (x : Fin n → ℝ) :
    exponentialProduct Exp v x ∈ S := by
  rw [exponentialProduct_eq_list_prod]
  apply S.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact hv i (x i)

theorem subgroup_eq_top_of_exponential_basis [PreconnectedSpace G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E) (S : Subgroup G)
    (hb : ∀ i (t : ℝ), Exp (t • b i) ∈ S) : S = ⊤ := by
  let d := b.equivFun.toContinuousLinearEquiv.symm
  have hcomb : tangentCombination b = d.toContinuousLinearMap := by
    ext x
    simp only [tangentCombination_apply]
    exact (b.equivFun_symm_apply x).symm
  have hd : HasMFDerivAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp b) 0 d.toContinuousLinearMap := by
    apply (hExp.hasMFDerivAt_exponentialProduct_zero b).congr_mfderiv
    exact hcomb
  have hmap := (locally_injective_open_of_mfderiv_equiv d
    (hExp.contMDiff_exponentialProduct b).contMDiffAt hd).2
  have hS : (S : Set G) ∈ 𝓝 (1 : G) := by
    rw [← hExp.exponentialProduct_zero b, ← hmap]
    change ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), exponentialProduct Exp b x ∈ S
    exact Eventually.of_forall (exponentialProduct_mem_subgroup S b hb)
  have hopen := S.isOpen_of_mem_nhds hS
  have hclosed := S.isClosed_of_isOpen hopen
  have hall : (S : Set G) = univ :=
    (show IsClopen (S : Set G) from ⟨hclosed, hopen⟩).eq_univ ⟨1, S.one_mem⟩
  exact SetLike.coe_injective hall

end PolycyclicRecognition

end

end OAI
