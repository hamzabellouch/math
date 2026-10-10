import OAI.Analysis.SegmentLenses.Embeddings

namespace OAI

/-!
# Primal isometries and coordinate completions
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

namespace SegmentEmbedding
variable {V W : Type*} [decidableEqV : DecidableEq V] [decidableEqW : DecidableEq W] [SegmentSystem V] [SegmentSystem W]


def testRestriction (e : SegmentEmbedding (V := V) (W := W)) : Test W →ₗ[ℝ] Test V where
  toFun u := Test.ofFinsupp (u.coeff.comapDomain e.toEmbedding e.toEmbedding.injective.injOn)
  map_add' u v := by apply Finsupp.ext; intro w; rfl
  map_smul' c u := by apply Finsupp.ext; intro w; rfl

@[simp] theorem testRestriction_apply (e : SegmentEmbedding (V := V) (W := W)) (u : Test W) (v : V) :
    (e.testRestriction u).coeff v = u.coeff (e.toEmbedding v) := by
  have _ := decidableEqV
  have _ := decidableEqW
  exact rfl

@[simp] theorem testRestriction_testMap (e : SegmentEmbedding (V := V) (W := W)) (u : Test V) :
    e.testRestriction (e.testMap u) = u := by
  apply Finsupp.ext
  intro v
  exact e.testMap_apply u v

theorem testMap_testRestriction (e : SegmentEmbedding (V := V) (W := W)) (u : Test W)
    (hu : ∀ w, w ∉ Set.range e.toEmbedding → u.coeff w = 0) :
    e.testMap (e.testRestriction u) = u := by
  have _ := decidableEqV
  have _ := decidableEqW
  change Finsupp.embDomain e.toEmbedding (u.coeff.comapDomain e.toEmbedding _) = u.coeff
  apply Finsupp.embDomain_comapDomain
  intro w hw
  by_contra hn
  exact Finsupp.mem_support_iff.mp hw (hu w hn)



theorem norm_testRestriction_le (e : SegmentEmbedding (V := V) (W := W)) (u : Test W) :
    ‖e.testRestriction u‖ ≤ ‖u‖ := by
  have _ := decidableEqV
  have _ := decidableEqW
  classical
  change segmentSeminorm V (e.testRestriction u).coeff ≤ _
  rw [segmentSeminorm_apply]
  apply ciSup_le
  intro F
  let pieces : F.sets → Finset W := fun S => S.val.map e.toEmbedding
  have hp : ∀ S, pieces S = ∅ ∨ SegmentSystem.isSegment (pieces S) :=
    fun S => Or.inr (e.map_segment S.val (F.segment _ S.property))
  have hd : Pairwise fun S T => Disjoint (pieces S) (pieces T) := by
    intro S T hST
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨v',hv',he⟩ := Finset.mem_map.mp hw'
    have he' := e.toEmbedding.injective he
    subst v'
    exact Finset.disjoint_left.mp (F.disjoint S.property T.property (fun h => hST (Subtype.ext h))) hv hv'
  have h := indexed_test_bound u.coeff pieces hp hd
  have he : F.seminorm (e.testRestriction u).coeff ^ 2 = ∑ S, (∑ w ∈ pieces S, u.coeff w)^2 := by
    rw [F.seminorm_sq]
    simp only [pieces, Finset.sum_map, testRestriction_apply]
  rw [← he] at h
  exact (sq_le_sq₀ (apply_nonneg _ _) (norm_nonneg u)).mp h

def primalRestriction (e : SegmentEmbedding (V := V) (W := W)) : Primal W →L[ℝ] Primal V :=
  ((UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V).comp
    (e.testRestriction.mkContinuous 1 (fun u => by simpa only [one_mul] using e.norm_testRestriction_le u))).extend
      UniformSpace.Completion.toComplL

@[simp] theorem primalRestriction_test (e : SegmentEmbedding (V := V) (W := W)) (u : Test W) :
    e.primalRestriction (u : Primal W) = (e.testRestriction u : Primal V) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) u

@[simp] theorem primalRestriction_primalMap (e : SegmentEmbedding (V := V) (W := W)) (x : Primal V) :
    e.primalRestriction (e.primalMap x) = x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (e.primalRestriction.continuous.comp e.primalMap.continuous) continuous_id) ?_
  intro u
  rw [e.primalMap_test, e.primalRestriction_test, e.testRestriction_testMap]

theorem norm_primalRestriction_le (e : SegmentEmbedding (V := V) (W := W)) (x : Primal W) :
    ‖e.primalRestriction x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le e.primalRestriction.continuous.norm continuous_norm) ?_
  intro u
  rw [e.primalRestriction_test, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact e.norm_testRestriction_le u

end SegmentEmbedding

section CompletionIsometries
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]



def completionIsometry (e : E ≃ₗᵢ[ℝ] F) :
    UniformSpace.Completion E ≃ₗᵢ[ℝ] UniformSpace.Completion F :=
  e.toLinearEquiv.extendOfIsometry
    (UniformSpace.Completion.toComplL : E →L[ℝ] UniformSpace.Completion E).toLinearMap
    (UniformSpace.Completion.toComplL : F →L[ℝ] UniformSpace.Completion F).toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun x => by
      change ‖(e x : UniformSpace.Completion F)‖ = ‖(x : UniformSpace.Completion E)‖
      rw [UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe, e.norm_map])

@[simp] theorem completionIsometry_coe (e : E ≃ₗᵢ[ℝ] F) (x : E) :
    completionIsometry e (x : UniformSpace.Completion E) = (e x : UniformSpace.Completion F) := by
  change completionIsometry e ((UniformSpace.Completion.toComplL : E →L[ℝ] UniformSpace.Completion E) x) = _
  unfold completionIsometry
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

end CompletionIsometries


section ClosureCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [completeSpaceE : CompleteSpace E]


theorem closureInclusion_dense (S : Submodule ℝ E) :
    DenseRange (Submodule.inclusion S.le_topologicalClosure) := by
  have _ := completeSpaceE
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨y,hy,hd⟩ := Metric.mem_closure_iff.mp x.property ε hε
  refine ⟨⟨y,hy⟩, ?_⟩
  exact hd



def completionClosureEquiv (S : Submodule ℝ E) :
    UniformSpace.Completion S ≃ₗᵢ[ℝ] S.topologicalClosure := by
  letI : CompleteSpace S.topologicalClosure := S.isClosed_topologicalClosure.completeSpace_coe
  exact (LinearEquiv.refl ℝ S).extendOfIsometry
    (UniformSpace.Completion.toComplL : S →L[ℝ] UniformSpace.Completion S).toLinearMap
    (Submodule.inclusion S.le_topologicalClosure)
    UniformSpace.Completion.denseRange_coe (closureInclusion_dense S)
    (fun x => by
      change ‖x‖ = ‖(x : UniformSpace.Completion S)‖
      rw [UniformSpace.Completion.norm_coe])

@[simp] theorem completionClosureEquiv_coe (S : Submodule ℝ E) (x : S) :
    completionClosureEquiv S (x : UniformSpace.Completion S) = Submodule.inclusion S.le_topologicalClosure x := by
  let : CompleteSpace S.topologicalClosure := S.isClosed_topologicalClosure.completeSpace_coe
  change completionClosureEquiv S ((UniformSpace.Completion.toComplL : S →L[ℝ] UniformSpace.Completion S) x) = _
  unfold completionClosureEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

end ClosureCompletion

section CoordinateCompletion
variable {V : Type*} [SegmentSystem V]



abbrev FiniteCoordinates (V : Type*) [SegmentSystem V] :=
  ↥(Submodule.span ℝ (Set.range (coordinate (V := V))))




local instance : UniformSpace (FiniteCoordinates V) :=
  (inferInstance : NormedAddCommGroup (FiniteCoordinates V)).toUniformSpace
local instance : AddCommGroup (FiniteCoordinates V) :=
  (inferInstance : NormedAddCommGroup (FiniteCoordinates V)).toAddCommGroup
local instance : Module ℝ (FiniteCoordinates V) :=
  (inferInstance : NormedSpace ℝ (FiniteCoordinates V)).toModule


def coordinateCompletionEquiv : UniformSpace.Completion (FiniteCoordinates V) ≃ₗᵢ[ℝ] CoordinatePredual V :=
  completionClosureEquiv (Submodule.span ℝ (Set.range (coordinate (V := V))))

@[simp] theorem coordinateCompletionEquiv_coe (x : FiniteCoordinates V) :
    (coordinateCompletionEquiv (x : UniformSpace.Completion (FiniteCoordinates V))).val = x.val := by
  exact congrArg (fun y : (Submodule.span ℝ (Set.range (coordinate (V := V)))).topologicalClosure =>
    (y : FullDual V)) (completionClosureEquiv_coe
      (Submodule.span ℝ (Set.range (coordinate (V := V)))) x)



theorem polar_norm (z : FullDual V) :
    ‖z‖ = ⨆ u : {u : Test V // ‖u‖ ≤ 1}, |z (u.val : Primal V)| := by
  let : Nonempty {u : Test V // ‖u‖ ≤ 1} := ⟨⟨0,by simp⟩⟩
  let S : Set ℝ := Set.range (fun u : {u : Test V // ‖u‖ ≤ 1} => |z (u.val : Primal V)|)
  have hb : BddAbove S := by
    refine ⟨‖z‖, ?_⟩
    rintro _ ⟨u,rfl⟩
    have h := z.le_opNorm (u.val : Primal V)
    rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at h
    exact h.trans (mul_le_of_le_one_right (norm_nonneg z) u.property)
  have h0 : (0:ℝ) ≤ ⨆ u : {u : Test V // ‖u‖ ≤ 1}, |z (u.val : Primal V)| := by
    have h := le_ciSup hb (⟨0, by simp⟩ : {u : Test V // ‖u‖ ≤ 1})
    change |z (0 : Primal V)| ≤ _ at h
    simpa only [map_zero,abs_zero] using h
  apply le_antisymm
  · apply dual_norm_le z h0
    intro u
    by_cases hu : u = 0
    · subst u
      change |z (0 : Primal V)| ≤ _
      simp
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let v : {u : Test V // ‖u‖ ≤ 1} := ⟨‖u‖⁻¹ • u, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
    have h := le_ciSup hb v
    have he : |z (v.val : Primal V)| = ‖u‖⁻¹ * |z (u : Primal V)| := by
      change |z ((‖u‖⁻¹ • u : Test V) : Primal V)| = _
      rw [UniformSpace.Completion.coe_smul, map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hn)]
    rw [he] at h
    have hm := mul_le_mul_of_nonneg_left h hn.le
    field_simp at hm
    simpa only [mul_comm] using hm
  · apply ciSup_le
    intro u
    have h := z.le_opNorm (u.val : Primal V)
    rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe] at h
    exact h.trans (mul_le_of_le_one_right (norm_nonneg z) u.property)

end CoordinateCompletion



end SegmentLenses

end

end OAI
