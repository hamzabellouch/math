import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalExponentialOpen
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRangeSubgroup

namespace OAI

/-! # Surjectivity of the nilpotent exponential from finite BCH

Local regularity gives a neighborhood in the exponential image. The binary
BCH formula makes that image a subgroup, so connectedness gives surjectivity.
No global exponential chart is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Set Filter
open scoped Manifold Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

omit [T2Space G] in
theorem range_exponential_mem_nhds_of_basis_formula
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {c n : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → GroupLieAlgebra (𝓘(ℝ, E)) G,
      (List.ofFn (fun i => Exp (X i))).prod = Exp (finiteDynkinPolynomial coeff X))
    (b : Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    range Exp ∈ 𝓝 (1 : G) := by
  let d : (Fin n → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv.trans
    (tangentSpaceCastModel (𝓘(ℝ, E)) (1 : G))
  have hcomb : tangentCombination (E := E) (fun i => (b i : E)) = d.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact (tangentCombination_apply (E := E) (fun i => (b i : E)) x).trans
      (b.equivFun_symm_apply x).symm
  obtain ⟨hf, hd⟩ := local_exponential_regularity_of_dynkin hExp coeff hprod b
  rw [hcomb] at hd
  have hm := (locally_injective_open_of_mfderiv_equiv d hf hd).2
  have hz : (Exp ∘ b.equivFun.symm) 0 = 1 := by
    simp only [Function.comp_apply, map_zero, hExp.map_zero]
  have hmem : range (Exp ∘ b.equivFun.symm) ∈ 𝓝 (1 : G) := by
    rw [← hz, ← hm]
    exact Filter.range_mem_map
  apply mem_of_superset hmem
  rintro _ ⟨x, rfl⟩
  exact ⟨b.equivFun.symm x, rfl⟩

theorem exponential_surjective_of_nilpotent_dynkin [PreconnectedSpace G]
    (dynkin : NilpotentDynkinExpansionInput E G)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    Function.Surjective Exp := by
  obtain ⟨c, hc⟩ := (isNilpotent_iff ℝ _ _).mp hnil
  let b := finBasis ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
  obtain ⟨coeffN, _, hprodN⟩ := dynkin Exp hExp c hc (finrank ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
  have hmem := range_exponential_mem_nhds_of_basis_formula hExp coeffN hprodN b
  obtain ⟨coeff, _, hprod⟩ := dynkin Exp hExp c hc 2
  apply exponential_surjective_of_range_mem_nhds hExp coeff (fun x y => ?_) hmem
  simpa only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, Matrix.cons_val_zero, Matrix.cons_val_succ] using hprod ![x, y]

end PolycyclicRecognition

end

end OAI
