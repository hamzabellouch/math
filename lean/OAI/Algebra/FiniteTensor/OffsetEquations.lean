import Mathlib
import OAI.Algebra.FiniteTensor.GermBranches
import OAI.Algebra.FiniteTensor.PolynomialApproximation

namespace OAI

/-! Finite offset equations and algebraic-germ Artin approximation. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ : Type*} [CommRing K] [Finite σ] [Finite τ]

 def independentOffset (a : σ → MvPowerSeries τ K) (i : σ) : MvPowerSeries (τ ⊕ σ) K :=
   rename Sum.inl (a i)+X (Sum.inr i)

 def offsetRetraction : τ ⊕ σ → MvPowerSeries σ K := Sum.elim (fun _=>0) X
 def graphRetraction : τ ⊕ σ → MvPowerSeries τ K := Sum.elim X (fun _=>0)

omit [Finite σ] in
 theorem independentOffset_zero (a : σ → MvPowerSeries τ K)
    (ha : ∀ i,constantCoeff (a i)=0) (i : σ) : constantCoeff (independentOffset a i)=0 := by
  simp [independentOffset,ha]

omit [Finite σ] [Finite τ] in
 theorem offsetRetraction_zero (i : τ ⊕ σ) : constantCoeff (offsetRetraction (K:=K) i)=0 := by
  cases i <;> simp [offsetRetraction]
omit [Finite σ] [Finite τ] in
 theorem graphRetraction_zero (i : τ ⊕ σ) : constantCoeff (graphRetraction (K:=K) i)=0 := by
  cases i <;> simp [graphRetraction]

 theorem subst_offsetRetraction_rename (f : MvPowerSeries τ K) :
    subst (offsetRetraction (K:=K) (σ:=σ)) (rename Sum.inl f)=C (constantCoeff f) := by
  rw [rename_eq_subst,subst_comp_subst_apply (HasSubst.X_comp _)
    (hasSubst_of_constantCoeff_zero offsetRetraction_zero)]
  have h : (fun s : τ=>subst (offsetRetraction (K:=K) (σ:=σ))
      ((X ∘ Sum.inl) s : MvPowerSeries (τ ⊕ σ) K))=0 := by
    funext s
    rw [Function.comp_apply,subst_X (hasSubst_of_constantCoeff_zero offsetRetraction_zero)]
    rfl
  rw [h,subst_zero_eq_C_constantCoeff]
  simp

 theorem subst_graphRetraction_rename (f : MvPowerSeries τ K) :
    subst (graphRetraction (K:=K) (σ:=σ)) (rename Sum.inl f)=f := by
  rw [rename_eq_subst,subst_comp_subst_apply (HasSubst.X_comp _)
    (hasSubst_of_constantCoeff_zero graphRetraction_zero)]
  have h : (fun s : τ=>subst (graphRetraction (K:=K) (σ:=σ))
      ((X ∘ Sum.inl) s : MvPowerSeries (τ ⊕ σ) K))=(X : τ → MvPowerSeries τ K) := by
    funext s
    rw [Function.comp_apply,subst_X (hasSubst_of_constantCoeff_zero graphRetraction_zero)]
    rfl
  rw [h,←map_algebraMap_eq_subst_X]
  simp

 theorem offset_retract (a : σ → MvPowerSeries τ K)
    (ha : ∀ i,constantCoeff (a i)=0) (F : MvPowerSeries σ K) :
    subst offsetRetraction (subst (independentOffset a) F)=F := by
  have hO := hasSubst_of_constantCoeff_zero (independentOffset_zero a ha)
  have hR := hasSubst_of_constantCoeff_zero (offsetRetraction_zero (K:=K) (τ:=τ) (σ:=σ))
  rw [subst_comp_subst_apply hO hR]
  have h : (fun i=>subst offsetRetraction (independentOffset a i))=(X : σ → MvPowerSeries σ K) := by
    funext i
    rw [independentOffset,←substAlgHom_apply hR,map_add,substAlgHom_apply,
      subst_offsetRetraction_rename,ha i,map_zero,zero_add,substAlgHom_X]
    rfl
  rw [h,←map_algebraMap_eq_subst_X]
  simp

 theorem graph_retract (a : σ → MvPowerSeries τ K)
    (ha : ∀ i,constantCoeff (a i)=0) (F : MvPowerSeries σ K) :
    subst graphRetraction (subst (independentOffset a) F)=subst a F := by
  have hO := hasSubst_of_constantCoeff_zero (independentOffset_zero a ha)
  have hR := hasSubst_of_constantCoeff_zero (graphRetraction_zero (K:=K) (τ:=τ) (σ:=σ))
  rw [subst_comp_subst_apply hO hR]
  have h : (fun i=>subst graphRetraction (independentOffset a i))=a := by
    funext i
    rw [independentOffset,←substAlgHom_apply hR,map_add,substAlgHom_apply,
      subst_graphRetraction_rename,substAlgHom_X]
    simp [graphRetraction]
  rw [h]

 
 theorem independentOffset_injective (a : σ → MvPowerSeries τ K)
    (ha : ∀ i,constantCoeff (a i)=0) : Function.Injective (subst (R:=K) (independentOffset a)) := by
  intro F G h
  have he := congrArg (subst (offsetRetraction (K:=K))) h
  simpa only [offset_retract a ha] using he

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries WithPiTopology
variable {K σ τ : Type*} [CommRing K] [Finite σ] [Finite τ]

 theorem graphRetraction_eq_killCompl (f : MvPowerSeries (τ ⊕ σ) K) :
    subst graphRetraction f=killCompl (Function.Embedding.inl : τ ↪ τ ⊕ σ) f := by
  let : UniformSpace K := ⊥
  let ε := killCompl (R:=K) (Function.Embedding.inl : τ ↪ τ ⊕ σ)
  have hε : Continuous ε := by
    apply continuous_pi
    intro d
    exact continuous_coeff K (Finsupp.embDomain Function.Embedding.inl d)
  have hvars : (fun i : τ ⊕ σ=>ε (X i))=graphRetraction := by
    funext i
    cases i with
    | inl i => exact killCompl_X i
    | inr i =>
      exact killCompl_X_eq_zero (by simp)
  have he := aeval_unique hε
  have hR := hasSubst_of_constantCoeff_zero (graphRetraction_zero (K:=K) (τ:=τ) (σ:=σ))
  change subst graphRetraction f=ε f
  rw [←AlgHom.congr_fun he f]
  rw [←substAlgHom_apply hR,substAlgHom_eq_aeval hR]
  simp only [coe_aeval]
  change eval₂ (algebraMap K (MvPowerSeries τ K)) graphRetraction f=
    eval₂ (algebraMap K (MvPowerSeries τ K)) (fun s=>ε (X s)) f
  rw [hvars]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ : Type*} [CommRing K] [Fintype σ] [Finite τ]

 

omit [Finite τ] in
theorem offset_kernel (f : MvPowerSeries (τ ⊕ σ) K)
    (hf : killCompl (Function.Embedding.inl : τ ↪ τ ⊕ σ) f=0) :
    ∃ q : σ → MvPowerSeries (τ ⊕ σ) K,f=∑ i,X (Sum.inr i)*q i := by
  classical
  let pick : (τ ⊕ σ →₀ ℕ) → Option σ := fun d=>
    if h : ∃ i,d (Sum.inr i)≠0 then some (Classical.choose h) else none
  have hpick (d : τ ⊕ σ →₀ ℕ) (i : σ) (hi : pick d=some i) : d (Sum.inr i)≠0 := by
    dsimp [pick] at hi
    split_ifs at hi with h
    · have he : Classical.choose h=i := Option.some.inj hi
      exact he ▸ Classical.choose_spec h
  let g : σ → MvPowerSeries (τ ⊕ σ) K := fun i d=>if pick d=some i then coeff d f else 0
  have hg (i : σ) : X (Sum.inr i)∣g i := by
    apply X_dvd_iff.mpr
    intro d hd
    change (if pick d=some i then coeff d f else 0)=0
    exact ite_eq_right (fun hi=>(hpick d i hi) hd)
  choose q hq using hg
  refine ⟨q,?_⟩
  conv_rhs => enter [2,i]; rw [←hq i]
  ext d
  simp only [map_sum]
  change coeff d f=∑ i,if pick d=some i then coeff d f else 0
  cases he : pick d with
  | some i => simp
  | none =>
    have hz : ∀ i,d (Sum.inr i)=0 := by
      intro i
      by_contra hi
      have hh : ∃ i,d (Sum.inr i)≠0 := ⟨i,hi⟩
      simp [pick,hh] at he
    have hd : d=Finsupp.embDomain (Function.Embedding.inl : τ ↪ τ ⊕ σ)
        (d.comapDomain Sum.inl Sum.inl_injective.injOn) := by
      ext s
      cases s <;> simp [hz]
    have hc := congrArg (coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn)) hf
    rw [coeff_killCompl,←hd,map_zero] at hc
    simp [hc]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ κ : Type*} [Field K] [CharZero K]
  [Fintype σ] [Finite τ] [Fintype κ]

omit [CharZero K] in
 theorem killCompl_mem_jet (e : σ ↪ τ) {f : MvPowerSeries τ K} (n : ℕ)
    (hf : f∈(jetIdeal (K:=K) (σ:=τ))^n) :
    killCompl e f∈(jetIdeal (K:=K) (σ:=σ))^n := by
  apply (mem_jetIdeal_pow_iff_coeff _ _).mpr
  intro d hd
  rw [coeff_killCompl]
  apply (mem_jetIdeal_pow_iff_coeff _ _).mp hf
  have he : (Finsupp.embDomain e d).degree=d.degree := by
    change (Finsupp.embDomain e d).sum (fun _ n=>n)=d.sum (fun _ n=>n)
    exact Finsupp.sum_embDomain
  rwa [he]

omit [CharZero K] in
 theorem centered_of_jet_close {a b : MvPowerSeries τ K} (n : ℕ) (hn : 1≤n)
    (ha : constantCoeff a=0) (h : b-a∈(jetIdeal (K:=K) (σ:=τ))^n) :
    constantCoeff b=0 := by
  have hh := (mem_jetIdeal_pow_iff_coeff _ _).mp h 0 (by simp only [map_zero]; omega)
  simpa only [map_sub,coeff_zero_eq_constantCoeff_apply,ha,sub_zero] using hh

 

omit [Fintype κ] in
 theorem exists_offset_relations (F : κ → MvPowerSeries σ K)
    (hF : ∀ k,IsAlgebraic (MvPolynomial σ K) (F k))
    (a : σ → MvPowerSeries τ K) (ha : ∀ i,constantCoeff (a i)=0)
    (hsol : ∀ k,subst a (F k)=0) :
    ∃ P : κ → Polynomial (MvPolynomial σ K),
      (∀ k,Polynomial.aeval (F k) (P k)=0) ∧
      (∀ k,subst (independentOffset a) (Polynomial.aeval (F k) (P k).derivative)≠0) ∧
      ∃ q : κ → σ → MvPowerSeries (τ ⊕ σ) K,
        ∀ k,subst (independentOffset a) (F k)=∑ i,X (Sum.inr i)*q k i := by
  classical
  have hi : Function.Injective (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K)) := by
    intro x y h
    apply MvPolynomial.coe_injective σ K
    simpa only [MvPowerSeries.algebraMap_apply',Algebra.algebraMap_self,
      MvPowerSeries.map_id,RingHom.id_apply] using h
  choose P hPn hP hD using fun k=>exists_relation_derivative_ne_zero hi (F k) (hF k)
  refine ⟨P,hP,?_,?_⟩
  · intro k hz
    apply hD k
    apply independentOffset_injective a ha
    simpa only [←substAlgHom_apply (hasSubst_of_constantCoeff_zero
      (independentOffset_zero a ha)),map_zero] using hz
  · have hq (k : κ) := offset_kernel (subst (independentOffset a) (F k)) (by
      rw [←graphRetraction_eq_killCompl,graph_retract a ha,hsol k])
    choose q hq using hq
    exact ⟨q,hq⟩

 

omit [CharZero K] [Fintype κ] in
 theorem offset_germ_soundness (F : κ → MvPowerSeries σ K)
    (P : κ → Polynomial (MvPolynomial σ K))
    (hP : ∀ k,Polynomial.aeval (F k) (P k)=0)
    (a : σ → MvPowerSeries τ K) (ha : ∀ i,constantCoeff (a i)=0)
    (hD : ∀ k,subst (independentOffset a) (Polynomial.aeval (F k) (P k).derivative)≠0)
    (n m : ℕ) (hm : 1 ≤ m) (hn : n ≤ m)
    (hprecision : ∀ k,(subst (independentOffset a)
      (Polynomial.aeval (F k) (P k).derivative)).order.toNat+1 ≤ m)
    (A : σ → MvPowerSeries (τ ⊕ σ) K)
    (G : κ → MvPowerSeries (τ ⊕ σ) K)
    (Q : κ → σ → MvPowerSeries (τ ⊕ σ) K)
    (hAalg : ∀ i,IsAlgebraic (MvPolynomial (τ ⊕ σ) K) (A i))
    (hA : ∀ i,A i-independentOffset a i∈(jetIdeal (K:=K) (σ:=τ ⊕ σ))^m)
    (hG : ∀ k,G k-subst (independentOffset a) (F k)∈(jetIdeal (K:=K) (σ:=τ ⊕ σ))^m)
    (hroot : ∀ k,(P k).eval₂ (MvPolynomial.aeval A).toRingHom (G k)=0)
    (hideal : ∀ k,G k=∑ i,X (Sum.inr i)*Q k i) :
    ∃ b : σ → MvPowerSeries τ K,
      (∀ i,constantCoeff (b i)=0) ∧ (∀ k,subst b (F k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  classical
  let := Fintype.ofFinite τ
  let e : τ ↪ τ ⊕ σ := Function.Embedding.inl
  let E := killCompl (R:=K) e
  let b := fun i=>E (A i)
  have hA0 : ∀ i,constantCoeff (A i)=0 := fun i=>
    centered_of_jet_close m hm (independentOffset_zero a ha i) (hA i)
  have hEa (i : σ) : E (independentOffset a i)=a i := by
    rw [←graphRetraction_eq_killCompl]
    have hR := hasSubst_of_constantCoeff_zero (graphRetraction_zero (K:=K) (τ:=τ) (σ:=σ))
    rw [independentOffset,←substAlgHom_apply hR,map_add,substAlgHom_apply,
      subst_graphRetraction_rename,substAlgHom_X]
    simp [graphRetraction]
  have hclose : ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^m := by
    intro i
    have h := killCompl_mem_jet e m (hA i)
    change E (A i-independentOffset a i)∈_ at h
    simpa only [map_sub,hEa] using h
  refine ⟨b,?_,?_,?_,?_⟩
  · intro i
    exact centered_of_jet_close m hm (ha i) (hclose i)
  · intro k
    have he : G k=subst A (F k) := germ_branch_stability (F k) (P k) (hP k)
      (independentOffset a) A (independentOffset_zero a ha) hA0 (hD k)
      (fun i=>Ideal.pow_le_pow_right (hprecision k) (hA i)) (G k)
      (Ideal.pow_le_pow_right (hprecision k) (hG k)) (hroot k)
    have hEG : E (G k)=0 := by
      rw [hideal k,map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [map_mul]
      have hz : E (X (Sum.inr i))=0 := killCompl_X_eq_zero (by simp [e])
      rw [hz,zero_mul]
    rw [he,←graphRetraction_eq_killCompl,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hA0)
        (hasSubst_of_constantCoeff_zero graphRetraction_zero)] at hEG
    convert hEG using 1
    congr 1
    funext i
    exact (graphRetraction_eq_killCompl (A i)).symm
  · intro i
    exact algebraic_killCompl e (hAalg i)
  · intro i
    exact Ideal.pow_le_pow_right hn (hclose i)

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K σ τ κ : Type*} [Field K] [CharZero K]
  [Fintype σ] [Finite τ] [Fintype κ]

abbrev OffsetVariables (σ κ : Type*) := σ ⊕ κ ⊕ (κ × σ)

def offsetPoint (A : σ → MvPowerSeries (τ ⊕ σ) K)
    (G : κ → MvPowerSeries (τ ⊕ σ) K)
    (Q : κ → σ → MvPowerSeries (τ ⊕ σ) K) :
    OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K :=
  Sum.elim A (Sum.elim G (fun p=>Q p.1 p.2))

def offsetCoeffHom : MvPolynomial σ K →+*
    MvPolynomial (OffsetVariables σ κ) (MvPolynomial (τ ⊕ σ) K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (fun i=>X (Sum.inl i))

def offsetRelation (P : Polynomial (MvPolynomial σ K)) (k : κ) :
    MvPolynomial (OffsetVariables σ κ) (MvPolynomial (τ ⊕ σ) K) :=
  P.eval₂ offsetCoeffHom (X (Sum.inr (Sum.inl k)))

def offsetIdealEquation (k : κ) :
    MvPolynomial (OffsetVariables σ κ) (MvPolynomial (τ ⊕ σ) K) :=
  X (Sum.inr (Sum.inl k))-
    ∑ i : σ,C (X (Sum.inr i))*X (Sum.inr (Sum.inr (k,i)))

def offsetEquations (P : κ → Polynomial (MvPolynomial σ K)) :
    κ ⊕ κ → MvPolynomial (OffsetVariables σ κ) (MvPolynomial (τ ⊕ σ) K) :=
  Sum.elim (fun k=>offsetRelation (P k) k) offsetIdealEquation

omit [CharZero K] [Fintype σ] [Finite τ] [Fintype κ] in
 theorem eval_offsetCoeffHom (v : OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K) :
    (MvPolynomial.aeval (R:=MvPolynomial (τ ⊕ σ) K) v).toRingHom.comp offsetCoeffHom=
      (MvPolynomial.aeval (fun i=>v (Sum.inl i))).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [offsetCoeffHom,MvPowerSeries.algebraMap_apply',MvPowerSeries.algebraMap_apply]
  · intro i
    simp [offsetCoeffHom]

omit [CharZero K] [Fintype σ] [Finite τ] [Fintype κ] in
 theorem eval_offsetRelation (v : OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K)
    (P : Polynomial (MvPolynomial σ K)) (k : κ) :
    MvPolynomial.aeval v (offsetRelation (τ:=τ) P k)=
      P.eval₂ (MvPolynomial.aeval (fun i=>v (Sum.inl i))).toRingHom (v (Sum.inr (Sum.inl k))) := by
  change (MvPolynomial.aeval v).toRingHom (P.eval₂ offsetCoeffHom _)=_
  rw [Polynomial.hom_eval₂,eval_offsetCoeffHom]
  simp

omit [CharZero K] [Finite τ] [Fintype κ] in
 theorem eval_offsetIdealEquation (v : OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K)
    (k : κ) :
    MvPolynomial.aeval v (offsetIdealEquation (K:=K) (τ:=τ) k)=
      v (Sum.inr (Sum.inl k))-
        ∑ i : σ,MvPowerSeries.X (Sum.inr i)*v (Sum.inr (Sum.inr (k,i))) := by
  simp [offsetIdealEquation,MvPowerSeries.algebraMap_apply']

omit [CharZero K] [Finite τ] [Fintype κ] in
 theorem offset_equations_iff (P : κ → Polynomial (MvPolynomial σ K))
    (v : OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K) :
    (∀ e,MvPolynomial.aeval v (offsetEquations (τ:=τ) P e)=0) ↔
    (∀ k,(P k).eval₂ (MvPolynomial.aeval (fun i=>v (Sum.inl i))).toRingHom
      (v (Sum.inr (Sum.inl k)))=0) ∧
    (∀ k,v (Sum.inr (Sum.inl k))=
      ∑ i : σ,MvPowerSeries.X (Sum.inr i)*v (Sum.inr (Sum.inr (k,i)))) := by
  simp only [Sum.forall,offsetEquations,Sum.elim_inl,Sum.elim_inr,
    eval_offsetRelation,eval_offsetIdealEquation,sub_eq_zero]

 

omit [CharZero K] [Fintype κ] in
 theorem offset_point_solves (F : κ → MvPowerSeries σ K)
    (P : κ → Polynomial (MvPolynomial σ K))
    (hP : ∀ k,Polynomial.aeval (F k) (P k)=0)
    (a : σ → MvPowerSeries τ K) (ha : ∀ i,MvPowerSeries.constantCoeff (a i)=0)
    (Q : κ → σ → MvPowerSeries (τ ⊕ σ) K)
    (hQ : ∀ k,MvPowerSeries.subst (independentOffset a) (F k)=
      ∑ i,MvPowerSeries.X (Sum.inr i)*Q k i) :
    ∀ e,MvPolynomial.aeval (offsetPoint (independentOffset a)
      (fun k=>MvPowerSeries.subst (independentOffset a) (F k)) Q)
      (offsetEquations (τ:=τ) P e)=0 := by
  apply (offset_equations_iff _ _).mpr
  constructor
  · intro k
    change (P k).eval₂ (MvPolynomial.aeval (independentOffset a)).toRingHom
      (MvPowerSeries.subst (independentOffset a) (F k))=0
    rw [aeval_relation_subst (F k) (P k) _ (independentOffset_zero a ha),hP k]
    rw [←MvPowerSeries.substAlgHom_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (independentOffset_zero a ha)),map_zero]
  · exact hQ

 

 theorem finite_offset_presentation (F : κ → MvPowerSeries σ K)
    (hF : ∀ k,IsAlgebraic (MvPolynomial σ K) (F k))
    (a : σ → MvPowerSeries τ K) (ha : ∀ i,MvPowerSeries.constantCoeff (a i)=0)
    (hsol : ∀ k,MvPowerSeries.subst a (F k)=0) (n : ℕ) :
    ∃ m : ℕ,n ≤ m ∧ ∃ f : κ ⊕ κ →
        MvPolynomial (OffsetVariables σ κ) (MvPolynomial (τ ⊕ σ) K),
      ∃ u : OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K,
        (∀ e,MvPolynomial.aeval u (f e)=0) ∧
        ∀ v : OffsetVariables σ κ → MvPowerSeries (τ ⊕ σ) K,
          (∀ e,MvPolynomial.aeval v (f e)=0) →
          (∀ i,IsAlgebraic (MvPolynomial (τ ⊕ σ) K) (v i)) →
          (∀ i,v i-u i∈(jetIdeal (K:=K) (σ:=τ ⊕ σ))^m) →
          ∃ b : σ → MvPowerSeries τ K,
            (∀ i,MvPowerSeries.constantCoeff (b i)=0) ∧
            (∀ k,MvPowerSeries.subst b (F k)=0) ∧
            (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
            ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  classical
  obtain ⟨P,hP,hD,Q,hQ⟩ := exists_offset_relations F hF a ha hsol
  let r := fun k=>(MvPowerSeries.subst (independentOffset a)
    (Polynomial.aeval (F k) (P k).derivative)).order.toNat+1
  let m := max n (1+Finset.univ.sup r)
  have hm : 1 ≤ m := le_trans (by omega) (le_max_right _ _)
  have hn : n ≤ m := le_max_left _ _
  have hr (k : κ) : r k ≤ m :=
    (Finset.le_sup (f:=r) (Finset.mem_univ k)).trans
      ((Nat.le_add_left _ _).trans (le_max_right _ _))
  refine ⟨m,hn,offsetEquations P,offsetPoint (independentOffset a)
    (fun k=>MvPowerSeries.subst (independentOffset a) (F k)) Q,
    offset_point_solves F P hP a ha Q hQ,?_⟩
  intro v hv halg hclose
  obtain ⟨hroot,hideal⟩ := (offset_equations_iff P v).mp hv
  exact offset_germ_soundness F P hP a ha hD n m hm hn hr
    (fun i=>v (Sum.inl i)) (fun k=>v (Sum.inr (Sum.inl k)))
    (fun k i=>v (Sum.inr (Sum.inr (k,i))))
    (fun i=>halg _) (fun i=>hclose _) (fun k=>hclose _) hroot hideal

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K σ τ κ : Type*} [Field K] [CharZero K]
  [Fintype σ] [Finite τ] [Fintype κ]

 

theorem algebraic_germ_artin (F : κ → MvPowerSeries σ K)
    (hF : ∀ k,IsAlgebraic (MvPolynomial σ K) (F k))
    (a : σ → MvPowerSeries τ K) (ha : ∀ i,MvPowerSeries.constantCoeff (a i)=0)
    (hsol : ∀ k,MvPowerSeries.subst a (F k)=0) (n : ℕ) :
    ∃ b : σ → MvPowerSeries τ K,
      (∀ i,MvPowerSeries.constantCoeff (b i)=0) ∧
      (∀ k,MvPowerSeries.subst b (F k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  classical
  obtain ⟨m,hn,f,u,hu,hsound⟩ := finite_offset_presentation F hF a ha hsol n
  obtain ⟨v,hv,hvalg,hvu⟩ := (polynomial_artin K (τ ⊕ σ)).finite f u hu m
  exact hsound v hv hvalg hvu

end
end PD4Tensor.Spreading
end

end OAI
