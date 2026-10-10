import OAI.Analysis.InterpolatedFactors.RelativeClosure

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

omit [DecidableEq α] in
 theorem repeat_coordinates_decay (i : α) (ξ : Fock α) :
    Tendsto (fun n => ξ (List.replicate n i)) atTop (𝓝 0) := by
  have hf : Function.Injective (fun n => List.replicate n i) := by
    intro n m h
    simpa only [List.length_replicate] using congrArg List.length h
  have hs : Summable (fun w : List α => ‖ξ w‖^2) := by
    simpa using (lp.memℓp ξ).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  have ht := (hs.comp_injective hf).tendsto_atTop_zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

 theorem semicircular_repeat_zero (i : α) :
    semicircular i (lp.single 2 [] 1)=lp.single 2 [i] 1 := by
  simp only [semicircular,add_apply,creation_single,annihilation_single_nil,add_zero]

 theorem semicircular_repeat_succ (i : α) (n : ℕ) :
    semicircular i (lp.single 2 (List.replicate (n+1) i) 1)=
      lp.single 2 (List.replicate (n+2) i) 1+lp.single 2 (List.replicate n i) 1 := by
  simp only [semicircular,add_apply,creation_single,List.replicate_succ,
    annihilation_single_cons,ite_true]

 theorem semicircular_eigen_root_zero (i : α) (z : ℂ) (ξ : Fock α)
    (hξ : semicircular i ξ=z • ξ) : ξ []=0 := by
  have he (n : ℕ) : inner ℂ (semicircular i (lp.single 2 (List.replicate n i) 1)) ξ=
      z*ξ (List.replicate n i) := by
    rw [← (semicircular_selfAdjoint i).star_eq,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left,hξ,inner_smul_right]
    simp [lp.inner_single_left,RCLike.inner_apply]
  have hb : (1:ℂ)*ξ (List.replicate 1 i)=z*ξ (List.replicate 0 i) := by
    have h := he 0
    rw [List.replicate_zero,semicircular_repeat_zero] at h
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,one_mul,
      List.replicate_one,List.replicate_zero] using h
  have ht (n : ℕ) : (1:ℂ)*ξ (List.replicate (n+2) i)=
      z*ξ (List.replicate (n+1) i)-(1:ℂ)*ξ (List.replicate n i) := by
    have h := he (n+1)
    rw [semicircular_repeat_succ] at h
    simp only [inner_add_left,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] at h
    linear_combination h
  exact JacobiNonatom.semicircular_eigenvector_zero 1 z one_ne_zero
    (fun n => ξ (List.replicate n i)) (repeat_coordinates_decay i ξ) hb ht 0

end

section
open MeasureTheory
variable {α : Type u_2} [DecidableEq α]
local instance : InnerProductSpace ℝ (Fock α) := InnerProductSpace.rclikeToReal ℂ (Fock α)

 theorem semicircular_spectral_noAtoms (i : α) :
    NullSingletonClass (CyclicSpectral.measure (semicircular i) (semicircular_selfAdjoint i) vacuum) := by
  apply CyclicSpectral.noAtoms
  intro r η hη
  have hc : semicircular i η=(r:ℂ) • η := by
    exact hη.trans (by
      apply Subtype.ext
      funext w
      change r • η w=(r:ℂ)*η w
      exact Complex.real_smul)
  have hz := semicircular_eigen_root_zero i (r:ℂ) η hc
  change (inner ℂ vacuum η).re=0
  simp only [vacuum,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,hz,Complex.zero_re]

end
section
open CyclicSpectral MeasureTheory
variable {α : Type u_3} [DecidableEq α]

instance scalarSpectral_probability (i : α) :
    IsProbabilityMeasure (measure (semicircular i) (semicircular_selfAdjoint i) (vacuum : Fock α)) :=
  probability _ _ _ (by simp [vacuum,lp.norm_single])

def scalarUniform (i : α) : UniformAlgebra →⋆ₐ[ℂ] Operator α := by
  letI := semicircular_spectral_noAtoms i
  exact uniformHom (semicircular i) (semicircular_selfAdjoint i) vacuum

theorem scalarUniform_state (i : α) (a : UniformAlgebra) :
    vacuumTrace (scalarUniform i a)=uniformState a := by
  let := semicircular_spectral_noAtoms i
  exact uniformHom_state _ _ _ a

theorem scalarUniform_mem (i : α) (a : UniformAlgebra) :
    scalarUniform i a∈(runAlgebra i).topologicalClosure := by
  let := semicircular_spectral_noAtoms i
  apply uniformHom_mem (semicircular i) (semicircular_selfAdjoint i) vacuum
    ((runAlgebra i).topologicalClosure) (StarSubalgebra.isClosed_topologicalClosure _) ?_ a
  apply StarSubalgebra.le_topologicalClosure
  change semicircular i∈runSpan i
  simpa [wick_semicircular_cons] using run_mem i 1

theorem scalarUniform_covariance {I : Type u_4} [DecidableEq I] (i j : I) (a : UniformAlgebra) :
    star (creation (some i))*scalarUniform (none : Option I) a*creation (some j)=
      if i=j then uniformState a • (1:Operator (Option I)) else 0 := by
  have h := closed_coarse_covariance (none : Option I) (some i) (some j)
    (by simp) (by simp) ⟨_,scalarUniform_mem none a⟩
  change _=vacuumTrace (scalarUniform (none:Option I) a) • (if some i=some j then 1 else 0) at h
  rw [scalarUniform_state] at h
  by_cases he : i=j
  · simpa only [he,ite_true] using h
  · simpa only [Option.some.injEq,ite_eq_right he,
      smul_zero (M := ℂ) (A := Operator (Option I))] using h

theorem scalarUniform_annihilation {I : Type u_5} [DecidableEq I] (i : I) (a : UniformAlgebra) :
    star (creation (some i)) (scalarUniform (none : Option I) a vacuum)=0 :=
  closed_coefficient_annihilation none (some i) (by simp) ⟨_,scalarUniform_mem none a⟩
end

open CyclicSpectral GaussianRecognition CircularRotation WeightedCornerIndex

abbrev ScalarIndex := Option (WeightedCornerIndex.Index × ℕ)
instance scalarIndexDecidableEq : DecidableEq ScalarIndex :=
  fun a b => @Option.instDecidableEq (WeightedCornerIndex.Index × ℕ)
    (fun x y => instDecidableEqProd x y) a b

def rotatedCreation (i : WeightedCornerIndex.Index × ℕ) : Operator ScalarIndex :=
  rotate (fun j => creation (some (j,i.2))) i.1

theorem rotatedCreation_covariance (i j : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (rotatedCreation i)*scalarUniform (none : ScalarIndex) a*rotatedCreation j=
      if i=j then uniformState a • (1:Operator ScalarIndex) else 0 := by
  rcases i with ⟨i,n⟩
  rcases j with ⟨j,m⟩
  by_cases hnm : n=m
  · subst m
    have hh := rotate_covariance (fun i : WeightedCornerIndex.Index => creation (some (i,n)))
      (scalarUniform (none : ScalarIndex) a) (uniformState a • (1:Operator ScalarIndex))
      (fun i j => by simpa only [Prod.mk.injEq,and_true] using scalarUniform_covariance (i,n) (j,n) a) i j
    simpa only [rotatedCreation,Prod.mk.injEq,and_true] using hh
  · have he (i j : WeightedCornerIndex.Index) :
        star (creation (some (i,n)))*scalarUniform (none : ScalarIndex) a*creation (some (j,m))=0 := by
      simpa only [Prod.mk.injEq,hnm,and_false,ite_false] using scalarUniform_covariance (i,n) (j,m) a
    simp only [Prod.mk.injEq,hnm,and_false,ite_false]
    rcases i with i | ⟨i,b⟩ <;> rcases j with j | ⟨j,c⟩
    · exact he (.inl i) (.inl j)
    · cases c <;> simp [rotatedCreation,rotate,plus,minus,mul_add,mul_sub,he]
    · cases b <;> simp only [rotatedCreation,rotate,plus,minus,star_smul,
        star_add (R := Operator ScalarIndex),star_sub (R := Operator ScalarIndex),add_mul,
        sub_mul,smul_mul_assoc (α := ℂ) (β := Operator ScalarIndex),he,
        smul_zero (M := ℂ) (A := Operator ScalarIndex),add_zero,sub_zero]
    · cases b <;> cases c <;>
        simp only [rotatedCreation,rotate,plus,minus,star_smul,
          star_add (R := Operator ScalarIndex),star_sub (R := Operator ScalarIndex),add_mul,
          sub_mul,mul_add,mul_sub,smul_mul_assoc (α := ℂ) (β := Operator ScalarIndex),
          mul_smul_comm (α := ℂ) (β := Operator ScalarIndex),he,
          smul_zero (M := ℂ) (A := Operator ScalarIndex),add_zero,sub_zero]

theorem rotatedCreation_annihilation (i : WeightedCornerIndex.Index × ℕ) (a : UniformAlgebra) :
    star (rotatedCreation i) (scalarUniform (none : ScalarIndex) a vacuum)=0 := by
  rcases i with ⟨i,n⟩
  rcases i with i | ⟨i,b⟩
  · exact scalarUniform_annihilation (I := WeightedCornerIndex.Index × ℕ) (.inl i,n) a
  · have hf := scalarUniform_annihilation (I := WeightedCornerIndex.Index × ℕ) (.inr (i,false),n) a
    have ht := scalarUniform_annihilation (I := WeightedCornerIndex.Index × ℕ) (.inr (i,true),n) a
    cases b <;> simp only [rotatedCreation,rotate,plus,minus,star_smul,
      star_add (R := Operator ScalarIndex),star_sub (R := Operator ScalarIndex),
      add_apply,sub_apply,smul_apply,hf,ht,smul_zero,add_zero,sub_zero]

def scalarSystem : GaussianRecognition.System UniformAlgebra (Fock ScalarIndex)
    (WeightedCornerIndex.Index × ℕ) uniformCovariance where
  coeff := scalarUniform none
  root := vacuum
  create := rotatedCreation
  contract i j a := by
    rw [rotatedCreation_covariance]
    by_cases h : i=j
    · simp only [uniformCovariance,h,ite_true,map_smul,map_one]
    · simp only [uniformCovariance,ite_eq_right h,map_zero]
  annihilate := rotatedCreation_annihilation

theorem scalar_weighted_state (u v : ℝ) (hv : 0<v) (hvu : v<u) (a : UniformAlgebra) :
    inner ℂ scalarSystem.root (scalarSystem.coeff a scalarSystem.root)=
      inner ℂ (WeightedFock.weightedSystem u v hv hvu).root
        ((WeightedFock.weightedSystem u v hv hvu).coeff a (WeightedFock.weightedSystem u v hv hvu).root) := by
  change vacuumTrace (scalarUniform (none : ScalarIndex) a)=
    inner ℂ WeightedFock.pRoot (WeightedFock.weightedUniform u v hv hvu a WeightedFock.pRoot)
  rw [scalarUniform_state,WeightedFock.weightedUniform_state]
end FreeGroupFactorMain.FreeFock

end

end OAI
