import Mathlib
import OAI.Analysis.WeakInfiniteness.InvariantSubspaces

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

universe u v

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma realState_nonneg {f : WeakDual ℝ (selfAdjoint A)} (hf : f ∈ realStateSpace A)
    {a : A} (ha : 0 ≤ a) : 0 ≤ f ⟨a,ha.isSelfAdjoint⟩ := by
  have h := (realStateComplexification f hf).map_nonneg ha
  rw [realStateComplexification_apply f hf ⟨a,ha.isSelfAdjoint⟩] at h
  exact (Complex.le_def.mp h).1

def annihilatorStates (S : Set A) : Set (WeakDual ℝ (selfAdjoint A)) :=
  {f | f ∈ realStateSpace A ∧ ∀ x ∈ S,∀ a : A,
    f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0}

lemma annihilatorStates_isCompact (S : Set A) : IsCompact (annihilatorStates S) := by
  apply (realStateSpace_isCompact A).inter_right
  show IsClosed {f : WeakDual ℝ (selfAdjoint A) | ∀ x ∈ S,∀ a : A,
    f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0}
  have he : {f : WeakDual ℝ (selfAdjoint A) | ∀ x ∈ S,∀ a : A,
    f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0} =
    ⋂ x : A,⋂ _hx : x ∈ S,⋂ a : A,{f : WeakDual ℝ (selfAdjoint A) |
      f ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0} := by
    ext f
    simp only [Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he]
  exact isClosed_iInter (fun x : A => isClosed_iInter (fun _hx : x ∈ S =>
    isClosed_iInter (fun a : A => isClosed_eq
      (WeakDual.eval_continuous (⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩ : selfAdjoint A))
      (continuous_const : Continuous (fun _ : WeakDual ℝ (selfAdjoint A) => (0 : ℝ))))))

lemma annihilatorStates_isExtreme (S : Set A) : IsExtreme ℝ (realStateSpace A) (annihilatorStates S) := by
  constructor
  · exact fun _ hf => hf.1
  · intro g hg k hk f hf hseg
    obtain ⟨t,s,ht,hs,hts,he⟩ := hseg
    have hz : ∀ x ∈ S,∀ a : A,g ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩=0 := by
      intro x hx a
      have hv := DFunLike.congr_fun he ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩
      change t*g _+s*k _=f _ at hv
      rw [hf.2 x hx a] at hv
      have hg0 := realState_nonneg hg (star_mul_self_nonneg (x*a))
      have hk0 := realState_nonneg hk (star_mul_self_nonneg (x*a))
      nlinarith
    exact ⟨hg,hz⟩

lemma annihilatorStates_gns_zero {S : Set A} {f : WeakDual ℝ (selfAdjoint A)}
    (hf : f ∈ annihilatorStates S) {x : A} (hx : x ∈ S) :
    (realStateComplexification f hf.1).gnsStarAlgHom x=0 := by
  let Φ := realStateComplexification f hf.1
  let Ω := gnsCyclicVector Φ
  have hzero : ∀ η : Φ.GNS,Φ.gnsStarAlgHom x η=0 :=
    isClosed_property (gnsAction_cyclic_dense Φ)
      (isClosed_eq (Φ.gnsStarAlgHom x).continuous continuous_const) (by
        intro a
        have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1)
          ⟨star (x*a)*(x*a),(star_mul_self_nonneg (x*a)).isSelfAdjoint⟩
        change representationVectorFunctional Φ.gnsStarAlgHom Ω _=f _ at he
        rw [representationVectorFunctional_square,hf.2 x hx a] at he
        have hn : Φ.gnsStarAlgHom (x*a) Ω=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
        simpa only [map_mul,mul_apply_eq_comp] using hn)
  ext η
  exact hzero η

theorem exists_extreme_annihilator_state {S : Set A} {g : WeakDual ℝ (selfAdjoint A)}
    (hg : g ∈ annihilatorStates S) (b : selfAdjoint A) :
    ∃ f ∈ (realStateSpace A).extremePoints ℝ,
      f ∈ annihilatorStates S ∧ g b ≤ f b := by
  let F := annihilatorStates S
  let T := {f ∈ F | ∀ h ∈ F,h b ≤ f b}
  have hT : T.Nonempty := by
    obtain ⟨f,hf,hm⟩ := (annihilatorStates_isCompact S).exists_isMaxOn ⟨g,hg⟩
      (WeakDual.eval_continuous b).continuousOn
    exact ⟨f,hf,hm⟩
  have he : IsExposed ℝ F T := by
    intro _
    exact ⟨realStateEvaluation b,rfl⟩
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℝ (selfAdjoint A))))
  obtain ⟨f,hf⟩ := (he.isCompact (annihilatorStates_isCompact S)).extremePoints_nonempty hT
  refine ⟨f,(annihilatorStates_isExtreme S).extremePoints_subset_extremePoints
    (he.isExtreme.extremePoints_subset_extremePoints hf),hf.1.1,hf.1.2 g hg⟩

end

end WeakPureInfiniteness
end

end OAI
