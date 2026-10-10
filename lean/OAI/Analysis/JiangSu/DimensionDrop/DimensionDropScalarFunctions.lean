import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropRestriction
import OAI.Analysis.JiangSu.CStarAlgebras.ClosedFunctionAlgebraGluing

namespace OAI

section

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace DimensionDropModel
open StarTerms ConcreteMatrixUnits ClosedFunctionAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
local instance (priority := 2000) functionSemiring : Semiring C(Interval,Mat I) :=
  (inferInstance : Ring C(Interval,Mat I)).toSemiring
local instance functionCStar : CStarAlgebra C(Interval,Mat I) := ContinuousMap.instCStarAlgebra
local instance matrixCFC : IsometricContinuousFunctionalCalculus ℝ (Mat I) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
local instance functionCFC : IsometricContinuousFunctionalCalculus ℝ C(Interval,Mat I) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
local instance functionSubringClass : SubringClass (StarSubalgebra ℂ C(Interval,Mat I)) C(Interval,Mat I) :=
  @StarSubalgebra.subringClass ℂ C(Interval,Mat I) _ _ _ _ _ _
local instance functionContinuousStar : ContinuousStar C(Interval,Mat I) := by
  let _ : CStarAlgebra C(Interval,Mat I) := inferInstance
  infer_instance
 def evaluation (t : Interval) : C(Interval,Mat I) →⋆ₐ[ℂ] Mat I where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
 def coordinate : C(Interval,Mat I) := ⟨fun t => (t:ℝ) • (1:Mat I),by fun_prop⟩
lemma functionValues_mem (p : I) (g : Gen I) : functionValues p g∈generated p :=
  StarSubalgebra.le_topologicalClosure _ ⟨.gen g,rfl⟩
lemma coordinate_mem (p : I) : (coordinate : C(Interval,Mat I))∈generated p := by
  have he : coordinate=(∑ i : I,functionValues p (.inl (i,i)))-
      ∑ i : I,(functionValues p (.inl (i,p))*functionValues p (.inr ())) *
        star (functionValues p (.inl (i,p))*functionValues p (.inr ())) := by
    apply ContinuousMap.ext
    intro t
    simp only [ContinuousMap.sub_apply,ContinuousMap.sum_apply,ContinuousMap.mul_apply,
      ContinuousMap.star_apply]
    exact (parameter_formula p t t.property.2).symm
  rw [he]
  exact sub_mem (sum_mem (fun i _ => functionValues_mem p _))
    (sum_mem (fun i _ => mul_mem (mul_mem (functionValues_mem p _) (functionValues_mem p _))
      (star_mem (mul_mem (functionValues_mem p _) (functionValues_mem p _)))))
lemma coordinate_selfadjoint : IsSelfAdjoint (coordinate : C(Interval,Mat I)) := by
  apply ContinuousMap.ext
  intro t
  change star ((t:ℝ) • (1:Mat I))=(t:ℝ) • (1:Mat I)
  simp only [star_smul,star_trivial,star_one]
 theorem scalar_mem (p : I) (g : C(Interval,ℝ)) : realScalar (A := Mat I) g∈generated p := by
  let G : ℝ→ℝ := fun r => g (Set.projIcc 0 1 (by norm_num) r)
  have hG : Continuous G := g.continuous.comp continuous_projIcc
  let _ : IsClosed (generated p : Set C(Interval,Mat I)) := StarSubalgebra.isClosed_topologicalClosure _
  have hm := cfc_mem (𝕜' := ℂ) (p := IsSelfAdjoint) G (coordinate_mem p)
  have he : cfc G (coordinate : C(Interval,Mat I))=realScalar g := by
    apply ContinuousMap.ext
    intro t
    have hx : IsSelfAdjoint ((evaluation (I := I) t) coordinate) := coordinate_selfadjoint.map _
    have hh := (evaluation (I := I) t).map_cfc G coordinate hG.continuousOn (map_continuous _)
      coordinate_selfadjoint hx
    change (evaluation t) (cfc G coordinate)=_
    rw [hh]
    change cfc G ((t:ℝ) • (1:Mat I))=g t • (1:Mat I)
    rw [←Algebra.algebraMap_eq_smul_one,cfc_algebraMap,Algebra.algebraMap_eq_smul_one]
    congr 1
    change g (Set.projIcc 0 1 _ (t:ℝ))=g t
    exact congrArg g (Set.projIcc_val _ t)
  rwa [he] at hm
end DimensionDropModel

end
end

section

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace DimensionDropModel
open ConcreteMatrixUnits StarTerms CompletelyPositiveOperations

variable {I : Type*} [Fintype I] [DecidableEq I]
 def algebraicFibre (p : I) (t : ℝ) : StarSubalgebra ℂ (Mat I) := evalRange (values p t)
lemma phi_mem_fibre (p : I) (t : ℝ) (i j : I) : phi t i j∈algebraicFibre p t := ⟨.gen (.inl (i,j)),rfl⟩
lemma s_mem_fibre (p : I) (t : ℝ) : s p t∈algebraicFibre p t := ⟨.gen (.inr ()),rfl⟩
lemma real_smul_mem_fibre {p : I} {t : ℝ} {a : Mat I} (ha : a∈algebraicFibre p t) (r : ℝ) :
    r • a∈algebraicFibre p t :=
  ((algebraicFibre p t).toSubalgebra.toSubmodule.restrictScalars ℝ).smul_mem r ha
lemma bridge_mem_fibre (p : I) {t : ℝ} (ht : t<1) (i : I) :
    amplify (J := I) (unit (some i) none)∈algebraicFibre p t := by
  have hm := mul_mem (phi_mem_fibre p t i p) (s_mem_fibre p t)
  rw [phi_mul_s,s_amplify] at hm
  have hz : Real.sqrt (1-t)≠0 := ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr ht))
  simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul] using real_smul_mem_fibre hm (Real.sqrt (1-t))⁻¹
lemma amplify_unit_mem_fibre (p : I) {t : ℝ} (ht : t<1) (a b : Option I) :
    amplify (J := I) (unit a b)∈algebraicFibre p t := by
  have hs (i : I) := bridge_mem_fibre p ht i
  have hst (i : I) : amplify (J := I) (unit none (some i))∈algebraicFibre p t := by
    simpa only [←map_star,unit_star] using star_mem (hs i)
  cases a with
  | none =>
    cases b with
    | none => simpa only [←map_mul,unit_mul,ite_true] using mul_mem (hst p) (hs p)
    | some j => exact hst j
  | some i =>
    cases b with
    | none => exact hs i
    | some j => simpa only [←map_mul,unit_mul,ite_true] using mul_mem (hs i) (hst j)
lemma amplify_mul_upper (a : Option I) (i j : I) :
    amplify (J := I) (unit a none)*unit (none,i) (none,j)=unit (a,i) (none,j) := by
  rw [amplify_unit,Finset.sum_mul]
  simp only [unit_mul,Prod.mk.injEq,true_and]
  simp
lemma upper_mul_amplify (a : Option I) (i j : I) :
    unit (none,i) (none,j)*amplify (J := I) (unit none a)=unit (none,i) (a,j) := by
  rw [amplify_unit,Finset.mul_sum]
  simp only [unit_mul,Prod.mk.injEq,true_and]
  simp
lemma amplify_upper_amplify (a b : Option I) (i j : I) :
    amplify (J := I) (unit a none)*unit (none,i) (none,j)*amplify (J := I) (unit none b)=unit (a,i) (b,j) := by
  rw [amplify_mul_upper,amplify_unit,Finset.mul_sum]
  simp only [unit_mul,Prod.mk.injEq,true_and]
  simp
lemma anchor_mul_phi (t : ℝ) (i j : I) :
    amplify (J := I) (unit (none : Option I) none)*phi t i j=t • unit (none,i) (none,j) := by
  rw [phi_amplify,mul_add,mul_smul_comm,amplify_mul_upper,←map_mul,unit_mul,ite_eq_right (by simp),map_zero,add_zero]
lemma upper_unit_mem_fibre (p : I) {t : ℝ} (ht0 : 0<t) (ht1 : t<1) (i j : I) :
    unit (none,i) (none,j)∈algebraicFibre p t := by
  have hm := mul_mem (amplify_unit_mem_fibre p ht1 none none) (phi_mem_fibre p t i j)
  rw [anchor_mul_phi] at hm
  simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt ht0),one_smul] using real_smul_mem_fibre hm t⁻¹
lemma matrix_expansion {J : Type*} [Fintype J] [DecidableEq J] (M : CStarMatrix J J ℂ) :
    M=∑ i,∑ j,(M i j) • unit i j := by
  ext a b
  simp [matrix_sum_apply,unit,CStarMatrix.ofMatrix_apply,Matrix.single_apply,ite_and]
lemma mem_of_units {J : Type*} [Fintype J] [DecidableEq J] {D : Type*} [CStarAlgebra D]
    (S : StarSubalgebra ℂ D) (π : CStarMatrix J J ℂ →⋆ₐ[ℂ] D)
    (h : ∀ i j,π (unit i j)∈S) (M : CStarMatrix J J ℂ) : π M∈S := by
  rw [matrix_expansion M]
  simp only [map_sum,map_smul]
  exact sum_mem (fun i _ => sum_mem (fun j _ => S.smul_mem (h i j) (M i j)))
 theorem interior_generation (p : I) {t : ℝ} (ht0 : 0<t) (ht1 : t<1) (M : Mat I) :
    M∈algebraicFibre p t := by
  apply mem_of_units (algebraicFibre p t) (StarAlgHom.id ℂ _) _ M
  rintro ⟨a,i⟩ ⟨b,j⟩
  change unit (a,i) (b,j)∈_
  rw [←amplify_upper_amplify]
  exact mul_mem (mul_mem (amplify_unit_mem_fibre p ht1 a none) (upper_unit_mem_fibre p ht0 ht1 i j))
    (amplify_unit_mem_fibre p ht1 none b)
 theorem lower_generation (p : I) (M : CStarMatrix (Option I) (Option I) ℂ) :
    amplify (J := I) M∈algebraicFibre p 0 :=
  mem_of_units _ _ (amplify_unit_mem_fibre p (by norm_num)) M
 theorem upper_generation (p : I) (M : CStarMatrix I I ℂ) : upperEmbed M∈algebraicFibre p 1 := by
  apply mem_of_units _ _ _ M
  intro i j
  rw [←phi_one]
  exact phi_mem_fibre p 1 i j
end DimensionDropModel

end
end

section

noncomputable section
open scoped ComplexOrder CStarAlgebra

namespace DimensionDropModel
open StarTerms ClosedFunctionAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
local instance generationFunctionCStar : CStarAlgebra C(Interval,Mat I) := ContinuousMap.instCStarAlgebra
 def leftEndpoint : Interval := ⟨0,by norm_num⟩
 def rightEndpoint : Interval := ⟨1,by norm_num⟩
 theorem endpoint_function_mem (p : I) (f : C(Interval,Mat I))
    (hl : ∃ a : CStarMatrix (Option I) (Option I) ℂ,amplify (J := I) a=f leftEndpoint)
    (hr : ∃ b : CStarMatrix I I ℂ,upperEmbed b=f rightEndpoint) : f∈generated p := by
  apply mem_of_fibrewise (generated p) (StarSubalgebra.isClosed_topologicalClosure _) (scalar_mem p) f
  intro t
  have hm : f t∈algebraicFibre p t := by
    by_cases h0 : (t:ℝ)=0
    · have ht : t=leftEndpoint := Subtype.ext h0
      rw [ht]
      obtain ⟨a,ha⟩ := hl
      rw [←ha]
      exact lower_generation p a
    by_cases h1 : (t:ℝ)=1
    · have ht : t=rightEndpoint := Subtype.ext h1
      rw [ht]
      obtain ⟨b,hb⟩ := hr
      rw [←hb]
      exact upper_generation p b
    exact interior_generation p (lt_of_le_of_ne t.property.1 (Ne.symm h0))
      (lt_of_le_of_ne t.property.2 h1) (f t)
  obtain ⟨e,he⟩ := hm
  refine ⟨realization p e,?_,he⟩
  rw [realization_eq_eval]
  exact StarSubalgebra.le_topologicalClosure _ ⟨e,rfl⟩
end DimensionDropModel

end
end

end OAI
