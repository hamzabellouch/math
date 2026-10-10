import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearNormApproximation

namespace OAI

section

noncomputable section
namespace NuclearNorm
open scoped ComplexOrder InnerProductSpace

section Cyclic
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma stateGNS_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a => f.gnsStarAlgHom a (Pureness.stateGNSVector f)) := by
  simp only [Pureness.stateGNS_apply_vector]
  exact UniformSpace.Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

end Cyclic

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure StateRow where
  size : ℕ
  left : Fin size → A
  right : Fin size → A

 def StateRow.map (f : A →ₚ[ℂ] ℂ) (R : StateRow (A := A)) :
    selfAdjoint A →ₗ[ℝ] selfAdjoint A :=
  NuclearTrace.coefficientSelfAdjMap f.gnsStarAlgHom
    (fun i => f.gnsStarAlgHom (R.left i) (Pureness.stateGNSVector f)) R.right

 lemma StateRow.map_apply (f : A →ₚ[ℂ] ℂ) (R : StateRow (A := A)) (x : selfAdjoint A) :
    (R.map f x : A) = ∑ i,∑ j, f (star (R.left i)*(x : A)*R.left j) •
      (star (R.right i)*R.right j) := by
  change (∑ i,∑ j, (⟪f.gnsStarAlgHom (R.left i) (Pureness.stateGNSVector f),
    f.gnsStarAlgHom (x : A) (f.gnsStarAlgHom (R.left j) (Pureness.stateGNSVector f))⟫_ℂ) •
      (star (R.right i)*R.right j)) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← Pureness.stateGNS_vector_value]
  simp only [map_mul,map_star,mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

 def StateRow.scale (R : StateRow (A := A)) (c : ℝ) : StateRow (A := A) :=
  {R with right := fun i => Real.sqrt c • R.right i}

 lemma StateRow.scale_map (f : A →ₚ[ℂ] ℂ) (R : StateRow (A := A)) {c : ℝ}
    (hc : 0 ≤ c) : (R.scale c).map f = c • R.map f := by
  ext x
  simp only [StateRow.map_apply,LinearMap.smul_apply,selfAdjoint.val_smul,StateRow.scale,
    star_smul,star_trivial,smul_mul_smul_comm,Real.mul_self_sqrt hc,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm _ _ _

 def stateRowSum (f : A →ₚ[ℂ] ℂ) (R : List (StateRow (A := A))) :
    selfAdjoint A →ₗ[ℝ] selfAdjoint A := (R.map (StateRow.map f)).sum

 lemma stateRowSum_scale (f : A →ₚ[ℂ] ℂ) (R : List (StateRow (A := A))) {c : ℝ}
    (hc : 0 ≤ c) : stateRowSum f (R.map (fun r => r.scale c)) = c • stateRowSum f R := by
  induction R with
  | nil => simp [stateRowSum]
  | cons r R ih =>
    simpa [stateRowSum,StateRow.scale_map f r hc,smul_add] using
      congrArg (fun z => c • r.map f + z) ih

 def stateRowCone (f : A →ₚ[ℂ] ℂ) :
    ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) where
  carrier := {L | ∃ R : List (StateRow (A := A)), L=stateRowSum f R}
  smul_mem' := by
    rintro c hc L ⟨R,rfl⟩
    exact ⟨R.map (fun r => r.scale c),(stateRowSum_scale f R hc.le).symm⟩
  add_mem' := by
    rintro L ⟨R,rfl⟩ M ⟨S,rfl⟩
    exact ⟨R++S,by simp [stateRowSum]⟩

 lemma stateRowCone_zero (f : A →ₚ[ℂ] ℂ) : (0 : selfAdjoint A →ₗ[ℝ] selfAdjoint A) ∈ stateRowCone f :=
  ⟨[],rfl⟩

 lemma stateRowCone_row (f : A →ₚ[ℂ] ℂ) (R : StateRow (A := A)) : R.map f ∈ stateRowCone f :=
  ⟨[R],by simp [stateRowSum]⟩

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma continuous_coefficient_tuple {K I : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) {n : ℕ} (c : Fin n → A) (x : I → selfAdjoint A) :
    Continuous (fun k : Fin n → K => fun i => NuclearTrace.coefficientSelfAdjMap α k c (x i)) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  change Continuous (fun k : Fin n → K => ∑ u,∑ v,
    (⟪k u,α (x i) (k v)⟫_ℂ) • (star (c u)*c v))
  fun_prop

 theorem nuclear_state_coefficient_approximation [Nontrivial A]
    (hA : Pureness.IsNuclear.{0,0} A) (f : A →ₚ[ℂ] ℂ)
    (hfaith : Function.Injective f.gnsStarAlgHom)
    {I : Type} [Fintype I] (x : I → selfAdjoint A) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : List (StateRow (A := A)), ‖x-fun i => stateRowSum f R (x i)‖ < ε := by
  classical
  let C := (stateRowCone f).map (NuclearTrace.evalTuple x)
  have h0 : (0 : I → selfAdjoint A) ∈ C := ⟨0,stateRowCone_zero f,by ext i; rfl⟩
  have hscale : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ C,t • s ∈ C := by
    intro t ht s hs
    obtain rfl | ht := ht.eq_or_lt
    · simpa using h0
    · exact C.smul_mem ht hs
  have hdual (F : (I → selfAdjoint A) →L[ℝ] ℝ)
      (_ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, |F y| ≤ c * normSeminorm ℝ (I → selfAdjoint A) y)
      (hFC : ∀ s ∈ C,F s ≤ 0) : F x ≤ 0 := by
    let l (i : I) : selfAdjoint A →L[ℝ] ℝ := F.comp (ContinuousLinearMap.single ℝ (fun _ : I => selfAdjoint A) i)
    obtain ⟨g,c,hg,hc,hl⟩ := finite_state_domination l
    have he (y : I → selfAdjoint A) : (∑ i,l i (y i))=F y := by
      change (∑ i,F (Pi.single i (y i)))=F y
      rw [←map_sum]
      congr 1
      exact Finset.univ_sum_single y
    rw [←he x]
    apply NuclearTrace.nuclear_coefficient_dual_bound hA f.gnsStarAlgHom hfaith g hg x
      (fun i => (l i).toLinearMap) hc hl
    intro n k a
    change (∑ i,l i _) ≤ 0
    rw [he]
    let D : (Fin n → f.GNS) → ℝ := fun k =>
      F (fun i => NuclearTrace.coefficientSelfAdjMap f.gnsStarAlgHom k a (x i))
    have hD : Continuous D := F.continuous.comp (continuous_coefficient_tuple _ a x)
    have hdense : DenseRange (fun d : Fin n → A => fun j =>
        f.gnsStarAlgHom (d j) (Pureness.stateGNSVector f)) :=
      DenseRange.piMap (fun _ => stateGNS_cyclic f)
    exact hdense.induction_on k (isClosed_le hD continuous_const) (fun d => by
      apply hFC
      exact ⟨(StateRow.mk n d a).map f,stateRowCone_row f _,rfl⟩)
  obtain ⟨s,hs,hclose⟩ := NuclearTrace.seminorm_cone_approximation_of_dual
    (normSeminorm ℝ (I → selfAdjoint A)) continuous_norm C C.convex h0 hscale x hdual hε
  obtain ⟨L,⟨R,rfl⟩,rfl⟩ := hs
  exact ⟨R,hclose⟩

 theorem simple_nuclear_state_coefficient_approximation [Nontrivial A]
    (hA : Pureness.IsNuclear.{0,0} A) (hsimple : Pureness.TopologicallySimple A)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    {I : Type} [Fintype I] (x : I → selfAdjoint A) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : List (StateRow (A := A)), ‖x-fun i => stateRowSum f R (x i)‖ < ε := by
  let : Nontrivial f.GNS := by
    refine ⟨⟨Pureness.stateGNSVector f,0,?_⟩⟩
    intro h
    have hn := Pureness.stateGNSVector_norm f hf
    rw [h,norm_zero] at hn
    exact zero_ne_one hn
  exact nuclear_state_coefficient_approximation hA f
    (CurrentMain.simple_starAlgHom_injective hsimple f.gnsStarAlgHom) x hε

end NuclearNorm

end
end

end OAI
