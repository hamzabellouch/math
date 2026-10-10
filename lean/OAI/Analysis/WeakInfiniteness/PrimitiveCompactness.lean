import Mathlib
import OAI.Analysis.WeakInfiniteness.StatePullback

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

universe u v w

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_state_annihilating_family {ι : Type w} (x : ι → A) (b : selfAdjoint A) (α : ℝ)
    (h : ∀ F : Finset ι,∃ f ∈ realStateSpace A,α ≤ f b ∧
      ∀ i ∈ F,∀ a : A,f ⟨star (x i*a)*(x i*a),(star_mul_self_nonneg (x i*a)).isSelfAdjoint⟩=0) :
    ∃ f ∈ annihilatorStates (Set.range x), α ≤ f b := by
  let C := {f ∈ realStateSpace A | α ≤ f b}
  let T : ι → Set (WeakDual ℝ (selfAdjoint A)) := fun i =>
    {f | ∀ a : A,f ⟨star (x i*a)*(x i*a),(star_mul_self_nonneg (x i*a)).isSelfAdjoint⟩=0}
  have hC : IsCompact C := (realStateSpace_isCompact A).inter_right
    (isClosed_le continuous_const (WeakDual.eval_continuous b))
  have hT : ∀ i,IsClosed (T i) := by
    intro i
    simp only [T,Set.ofPred_forall]
    exact isClosed_iInter (fun a => isClosed_eq (WeakDual.eval_continuous _) continuous_const)
  obtain ⟨f,hfC,hfT⟩ := hC.inter_iInter_nonempty T hT (by
    intro F
    obtain ⟨g,hg,hgb,hgT⟩ := h F
    refine ⟨g,⟨hg,hgb⟩,?_⟩
    simpa only [Set.mem_iInter,T,Set.mem_ofPred_eq] using hgT)
  refine ⟨f,⟨hfC.1,?_⟩,hfC.2⟩
  rintro _ ⟨i,rfl⟩ a
  exact (Set.mem_iInter.mp hfT i) a

theorem finite_norm_support_cover {ι : Type w} (x : ι → A) (b : A) (hb : 0 ≤ b)
    (α : ℝ) (hα : 0 < α)
    (hcover : ∀ (f : WeakDual ℝ (selfAdjoint A)) (hf : f ∈ (realStateSpace A).extremePoints ℝ),
      α ≤ ‖(realStateComplexification f hf.1).gnsStarAlgHom b‖ →
        ∃ i, (realStateComplexification f hf.1).gnsStarAlgHom (x i) ≠ 0) :
    ∃ F : Finset ι,∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)),α ≤ ‖π b‖ → ∃ i ∈ F,π (x i) ≠ 0 := by
  classical
  by_contra! hn
  have hfinite : ∀ F : Finset ι,∃ f ∈ realStateSpace A,α ≤ f ⟨b,hb.isSelfAdjoint⟩ ∧
      ∀ i ∈ F,∀ a : A,f ⟨star (x i*a)*(x i*a),(star_mul_self_nonneg (x i*a)).isSelfAdjoint⟩=0 := by
    intro F
    obtain ⟨H,hH,hI,hC,π,hπ,hF⟩ := hn F
    have hbn : π b ≠ 0 := by
      intro hz
      rw [hz,norm_zero] at hπ
      exact (not_le_of_gt hα) hπ
    let : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne (π b) 0 hbn
    obtain ⟨f,hf,hfb⟩ := exists_annihilator_norming_pullback π (x '' (F : Set ι))
      (by rintro _ ⟨i,hi,rfl⟩; exact hF i hi) b hb
    refine ⟨f,hf.1,by rwa [hfb],?_⟩
    intro i hi a
    exact hf.2 (x i) ⟨i,hi,rfl⟩ a
  obtain ⟨g,hg,hgb⟩ := exists_state_annihilating_family x ⟨b,hb.isSelfAdjoint⟩ α hfinite
  obtain ⟨f,hf,hfS,hfb⟩ := exists_extreme_annihilator_state hg ⟨b,hb.isSelfAdjoint⟩
  let Φ := realStateComplexification f hf.1
  have he : f ⟨b,hb.isSelfAdjoint⟩ ≤ ‖Φ.gnsStarAlgHom b‖ := by
    let Ω := gnsCyclicVector Φ
    have hΩ : ‖Ω‖=1 := norm_gnsCyclicVector Φ (realStateComplexification_one f hf.1)
    have hv := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1) ⟨b,hb.isSelfAdjoint⟩
    change (inner ℂ Ω (Φ.gnsStarAlgHom b Ω)).re=f ⟨b,hb.isSelfAdjoint⟩ at hv
    calc
      _ = (inner ℂ Ω (Φ.gnsStarAlgHom b Ω)).re := hv.symm
      _ ≤ ‖inner ℂ Ω (Φ.gnsStarAlgHom b Ω)‖ := Complex.re_le_norm _
      _ ≤ ‖Ω‖*‖Φ.gnsStarAlgHom b Ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖Ω‖*(‖Φ.gnsStarAlgHom b‖*‖Ω‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖Φ.gnsStarAlgHom b‖ := by rw [hΩ,one_mul,mul_one]
  obtain ⟨i,hi⟩ := hcover f hf (hgb.trans (hfb.trans he))
  exact hi (annihilatorStates_gns_zero hfS ⟨i,rfl⟩)

end

end WeakPureInfiniteness
end

end OAI
