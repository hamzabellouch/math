import OAI.Analysis.ForestSpace.Components

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section CoordinateDensity
variable {V : Type} [PartialOrder V]

 theorem headJ_finite_eq_sum (H : Finset V) (hH : IsLowerSet (H : Set V)) (u : J V) :
    headJ (H : Set V) hH u = ∑ v ∈ H, eStar v u • e v := by
  refine UniformSpace.Completion.induction_on u (isClosed_eq (headJ (H : Set V) hH).continuous
    (continuous_finsetSum _ (fun v hv => (eStar v).continuous.smul continuous_const))) ?_
  intro f
  rw [headJ_coe,TestVector.cut_finite_eq_sum]
  change (UniformSpace.Completion.toComplL : TestVector V →L[ℝ] J V) (∑ v ∈ H, f v • TestVector.single v 1) = _
  simp only [map_sum,map_smul,eStar_coe]
  rfl

 theorem exists_headJ_approx (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (u : J V) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset V, ∃ hH : IsLowerSet (H : Set V), ‖u-headJ (H : Set V) hH u‖ < ε := by
  obtain ⟨z,hz,hclose⟩ := Metric.mem_closure_iff.mp
    (UniformSpace.Completion.denseRange_coe u) ε hε
  obtain ⟨f,rfl⟩ := hz
  obtain ⟨H,hSH,hH⟩ := exists_finite_lower_hull hAnc f.toFinsupp.support
  have hf : SupportedOn f (H : Set V) := by
    intro v hv
    exact Finsupp.notMem_support_iff.mp (fun hs => hv (hSH hs))
  have he : tailJ (H : Set V) hH (f : J V) = 0 := by
    change (f : J V) - headJ (H : Set V) hH (f : J V) = 0
    rw [headJ_coe,TestVector.cut_eq_self hf,sub_self]
  have hn := norm_tailJ_le (H : Set V) hH (u - (f : J V))
  rw [map_sub,he,sub_zero] at hn
  refine ⟨H,hH,hn.trans_lt ?_⟩
  simpa only [dist_eq_norm] using hclose

 theorem eq_zero_of_coordinates_zero (hAnc : ∀ v : V, (Set.Iic v).Finite)
    {u : J V} (hu : ∀ v, eStar v u = 0) : u = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨H,hH,hh⟩ := exists_headJ_approx hAnc u ε hε
  have he : headJ (H : Set V) hH u = 0 := by
    rw [headJ_finite_eq_sum]
    simp only [hu,zero_smul,Finset.sum_const_zero]
  simpa only [he,sub_zero,zero_add] using hh

 theorem coordinateSubspace_eq_top_of_reflexive (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (hRefl : Reflexive (J V)) : coordinateSubspace V = ⊤ := by
  let M := coordinateSubspace V
  let : IsClosed (M : Set (FullDual V)) := Submodule.isClosed_topologicalClosure _
  let : NormedAddCommGroup ((FullDual V) ⧸ M) := inferInstance
  let : NormedSpace ℝ ((FullDual V) ⧸ M) := inferInstance
  apply top_unique
  intro x hx
  change x ∈ M
  apply (Submodule.Quotient.mk_eq_zero M).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ψ
  obtain ⟨u,hu⟩ := hRefl (ψ.comp M.mkQL)
  have hz : ∀ v, eStar v u = 0 := by
    intro v
    have hv : eStar v ∈ M := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨v,rfl⟩)
    have hh := congrArg (fun z : StrongDual ℝ (FullDual V) => z (eStar v)) hu
    change eStar v u = ψ (M.mkQ (eStar v)) at hh
    simpa only [Submodule.mkQ_apply,(Submodule.Quotient.mk_eq_zero M).mpr hv,map_zero] using hh
  have hu0 := eq_zero_of_coordinates_zero hAnc hz
  have hh := congrArg (fun z : StrongDual ℝ (FullDual V) => z x) hu
  change x u = ψ (M.mkQ x) at hh
  simpa only [Submodule.mkQ_apply,hu0,map_zero] using hh.symm

 theorem forest_coordinateSubspace_eq_top : coordinateSubspace Vertex = ⊤ :=
  coordinateSubspace_eq_top_of_reflexive Vertex.finiteAncestors reflexive_forest_J

noncomputable def fullDualEquiv : X Vertex ≃ₗᵢ[ℝ] FullDual Vertex :=
  LinearIsometryEquiv.ofSurjective (coordinateSubspace Vertex).subtypeₗᵢ (by
    intro x
    exact ⟨⟨x,by rw [forest_coordinateSubspace_eq_top]; trivial⟩,rfl⟩)

 theorem reflexive_main_fullDual : Reflexive (FullDual Vertex) :=
  reflexive_dual reflexive_forest_J

 theorem separable_main_fullDual : TopologicalSpace.SeparableSpace (FullDual Vertex) := by
  let := separable_X (V := Vertex)
  exact fullDualEquiv.surjective.denseRange.separableSpace fullDualEquiv.continuous

 theorem infiniteDimensional_main_fullDual : ¬FiniteDimensional ℝ (FullDual Vertex) := by
  intro h
  let := h
  have : Finite Vertex := linearIndependent_eStar.finite
  exact Infinite.not_finite (inferInstance : Finite Vertex)

 theorem exists_main_head_approx (x : FullDual Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Finset Vertex, ∃ hH : IsLowerSet (H : Set Vertex),
      ‖x-P (H : Set Vertex) hH x‖ < ε := by
  let z : X Vertex := fullDualEquiv.symm x
  obtain ⟨H,hH,hh⟩ := exists_head_approx Vertex.finiteAncestors z ε hε
  refine ⟨H,hH,?_⟩
  have hz : (z : FullDual Vertex) = x := fullDualEquiv.apply_symm_apply x
  change ‖(z : FullDual Vertex)-P (H : Set Vertex) hH z‖ < ε at hh
  simpa only [hz] using hh

end CoordinateDensity

section MainNorm

noncomputable def mainFiniteCoordinates (H : Finset Vertex) : FullDual Vertex →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun v : H => (ContinuousLinearMap.apply ℝ ℝ) (e (v : Vertex)))

 theorem mainFiniteCoordinates_kernel_finite (H : Finset Vertex) :
    FiniteDimensional ℝ ((FullDual Vertex) ⧸ (mainFiniteCoordinates H).toLinearMap.ker) :=
  Module.Finite.equiv (mainFiniteCoordinates H).toLinearMap.quotKerEquivRange.symm

 theorem main_P_eq_zero_of_mem_ker (H : Finset Vertex) (hH : IsLowerSet (H : Set Vertex))
    {y : FullDual Vertex} (hy : y ∈ (mainFiniteCoordinates H).toLinearMap.ker) :
    P (H : Set Vertex) hH y = 0 := by
  have hh : mainFiniteCoordinates H y = 0 := hy
  rw [P_finite_eq_sum]
  apply Finset.sum_eq_zero
  intro v hv
  have hz : y (e v) = 0 := congrFun hh ⟨v,hv⟩
  rw [hz,zero_smul]

 theorem main_average_modulus (t : ℝ) (ht : 0 < t) :
    Real.sqrt (1+t^2/12)-1 ≤ averageModulus (FullDual Vertex) norm t := by
  apply averageModulus_lower_of_subspaces infiniteDimensional_main_fullDual ht.le
  intro x hx ε hε
  obtain ⟨H,hH,hclose⟩ := exists_main_head_approx x (ε/4) (by positivity)
  let F : Cofinite (FullDual Vertex) := ⟨(mainFiniteCoordinates H).toLinearMap.ker,
    (mainFiniteCoordinates H).isClosed_ker, mainFiniteCoordinates_kernel_finite H⟩
  refine ⟨F,?_⟩
  intro y hy hyn
  have he : Q (H : Set Vertex) hH y = y := by
    rw [Q_eq_sub,main_P_eq_zero_of_mem_ker H hH hy,sub_zero]
  have hy' : Annihilates y (H : Set Vertex) := by
    rw [← he]
    exact annihilates_Q _ _ _
  have hpair := paired_estimate Vertex.forestOrder Vertex.finiteAncestors (H : Set Vertex) hH
    (P (H : Set Vertex) hH x) (t • y) (annihilates_P _ _ _) (hy'.smul t)
  rw [norm_smul,Real.norm_of_nonneg ht.le,hyn,mul_one] at hpair
  have hh := pair_perturbation x (P (H : Set Vertex) hH x) (t • y)
    (t^2/12) (by positivity) hx hpair
  linarith

 theorem main_auc_modulus_zero {α β : ℝ} (R : EquivalentNorm (FullDual Vertex) α β) :
    aucModulus (FullDual Vertex) R.N (α/(2*β)) = 0 := by
  apply R.bounded_trees_auc_zero infiniteDimensional_main_fullDual
    (fun h s => (Vertex.treePath h s : FullDual Vertex))
  · exact Vertex.norm_treePath
  · intro h hh s hs j
    change 1 ≤ ‖((Vertex.treePath h (s++[j])-Vertex.treePath h s : X Vertex) : FullDual Vertex)‖
    rw [Vertex.treePath_child h hh s hs j,eX_val,norm_eStar]
  · intro h hh s hs
    have hd := weakNull_coordinates _
      (Vertex.child_injective (Vertex.node h hh s (Nat.le_of_lt hs)) hs)
    intro φ
    have hh' := hd (φ.comp (coordinateSubspace Vertex).subtypeL)
    convert hh' using 1
    ext j
    change φ (((Vertex.treePath h (s++[j])-Vertex.treePath h s : X Vertex) : FullDual Vertex)) = _
    rw [Vertex.treePath_child h hh s hs j]
    rfl


 theorem main_no_equivalent_AUC {α β : ℝ} (R : EquivalentNorm (FullDual Vertex) α β) :
    ¬IsAUC R.N := by
  intro h
  have hp : 0 < α/(2*β) := div_pos R.alpha_pos (mul_pos (by norm_num) (R.alpha_pos.trans_le R.alpha_le_beta))
  have hh := h _ hp
  rw [main_auc_modulus_zero R] at hh
  exact lt_irrefl _ hh

end MainNorm

end

end ForestSpace

end OAI
