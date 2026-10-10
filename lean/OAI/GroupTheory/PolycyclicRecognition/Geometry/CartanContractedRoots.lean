import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContractedNilpotentFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGlobalGeneratorWords

namespace OAI

/-! # The Cartan subgroup and its contracted root directions generate the group

Each nonzero generalized root contracts in a suitable Cartan direction. The
nilpotent part of the adjoint operator is retained. The already constructed
finite root words and Cartan factorization then prove generation.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
open scoped Manifold Matrix.Norms.Operator Topology

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
theorem root_exp_mem_contracted_cartan
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (v : rootSpace H χ) : ExpG v ∈ contractedBy F.inclusionD.range := by
  let : TopologicalSpace (rootSpace H χ) :=
    (inferInstance : NormedAddCommGroup (rootSpace H χ)).toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, τ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hτ : Function.Injective τ := by
    intro g k he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  let Exp : rootSpace H χ → G := fun w => ExpG w
  have hc : Continuous Exp := by
    apply hind.continuous_iff.mpr
    change Continuous (fun w : rootSpace H χ => (τ (ExpG w) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let N := rootAction H χ h + 1
  have hn : _root_.IsNilpotent N := by
    simpa only [hh, neg_smul, one_smul, sub_neg_eq_add, N] using
      rootAction_nilpotent_correction H χ h
  obtain ⟨c, hcN⟩ := hn
  have hN : N ^ (c + 1) = 0 := by rw [pow_succ, hcN, zero_mul]
  let d : ℝ → F.inclusionD.range := fun t =>
    ⟨F.inclusionD (F.ExpD (F.D.equiv ((-t) • h))), ⟨_, rfl⟩⟩
  have hd (t : ℝ) : (d t : G) = ExpG (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
    dsimp [d]
    rw [F.compatibleD]
    change ExpG ((-t) • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = _
    rw [neg_smul]
  let A : ℝ → rootSpace H χ → rootSpace H χ :=
    fun t w => (NormedSpace.exp (t • rootAction H χ h)) w
  have hA (w : rootSpace H χ) :
      Filter.Tendsto (fun t => A t w) Filter.atTop (𝓝 0) := by
    have he : rootAction H χ h = N - 1 := by simp [N]
    simp only [A, he, exp_smul_sub_one, smul_apply]
    exact tendsto_contracted_nilpotent_flow N hN w
  apply contractedBy_of_continuous_flow F.inclusionD.range Exp hc
    (by simpa [Exp] using hExpG.map_zero) d A _ hA v
  intro w t _
  apply hτ
  simp only [Exp, map_mul, map_inv, hd, hmatch, map_neg, map_smul]
  exact represented_root_exp_inverse_conjugation H χ j h t w

namespace CartanWordModel

include T in
theorem cartan_and_contracted_generate (M : CartanWordModel H)
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier) :
    Subgroup.closure ((F.inclusionD.range : Set G) ∪ contractedBy F.inclusionD.range) = ⊤ := by
  let K := Subgroup.closure ((F.inclusionD.range : Set G) ∪ contractedBy F.inclusionD.range)
  obtain ⟨n, hn⟩ := M.exists_global_cartan_generator_words T F hExpG realize haarN dynkinN
    (Module.finBasis ℝ (cartanRootIdeal H))
  have hletter (i : Fin M.letterCount) (s : ℝ) :
      F.inclusionN (F.ExpN (F.N.equiv (s • M.letter i))) ∈ K := by
    rw [F.compatibleN]
    apply Subgroup.subset_closure
    right
    exact root_exp_mem_contracted_cartan T F hExpG realize (M.weight i) (M.weight_nonzero i)
      ⟨(s • M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G),
        (rootSpace H (M.weight i)).smul_mem s (M.letter_root i)⟩
  have hN (x : F.N.carrier) : F.inclusionN x ∈ K := by
    obtain ⟨u, _, hu⟩ := hn x
    rw [← hu]
    simp only [generatorGroupWord, map_list_prod, List.map_map, Function.comp_def]
    apply K.list_prod_mem
    intro z hz
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hz
    exact hletter p.1 p.2
  apply top_unique
  intro g _
  obtain ⟨⟨x, d⟩, rfl⟩ := F.surjective g
  exact K.mul_mem (hN x) (Subgroup.subset_closure (Or.inl ⟨d, rfl⟩))

end CartanWordModel
end PolycyclicRecognition

end

end OAI
