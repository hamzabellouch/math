import Mathlib
import OAI.Algebra.FiniteTensor.JetTopology

namespace OAI

/-! Regular linear charts and polynomial compatibility of coordinate changes. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
open MvPolynomial

 
theorem totalDegree_eval₂_linear {K σ τ : Type*} [CommSemiring K]
    (p : MvPolynomial σ K) (q : σ → MvPolynomial τ K)
    (hq : ∀ i,(q i).totalDegree≤1) :
    (eval₂ C q p).totalDegree≤p.totalDegree := by
  classical
  have hm (d : σ →₀ ℕ) (c : K) :
      (eval₂ C q (monomial d c)).totalDegree≤d.sum (fun _ e=>e) := by
    rw [eval₂_monomial]
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C,zero_add]
    apply (totalDegree_finsetProd d.support _).trans
    apply Finset.sum_le_sum
    intro i hi
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hq i))
  change ((eval₂Hom C q) p).totalDegree≤p.totalDegree
  conv_lhs => rw [p.as_sum,map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  exact (hm d _).trans (le_totalDegree hd)

 
theorem coe_eval₂_polynomials {K σ τ : Type*} [CommRing K]
    (p : MvPolynomial σ K) (q : σ → MvPolynomial τ K) :
    ((eval₂ C q p : MvPolynomial τ K) : MvPowerSeries τ K) =
      MvPowerSeries.subst (fun i=>(q i : MvPowerSeries τ K)) (p : MvPowerSeries σ K) := by
  rw [MvPowerSeries.subst_coe]
  have he : MvPolynomial.coeToMvPowerSeries.ringHom.comp (eval₂Hom C q) =
      (aeval (fun i=>(q i : MvPowerSeries τ K))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [MvPowerSeries.algebraMap_apply]
    · intro i
      simp
  exact RingHom.congr_fun he p

 

theorem exists_nonzero_line {K σ : Type*} [Field K] [Infinite K] [Finite σ]
    (f : MvPowerSeries σ K) (hf : f≠0) :
    ∃ a : σ → K,MvPowerSeries.subst
      (fun i=>MvPowerSeries.C (a i)*MvPowerSeries.X ()) f≠0 := by
  classical
  obtain ⟨d,hd⟩ : ∃ d, MvPowerSeries.coeff d f≠0 := by
    by_contra h
    push Not at h
    exact hf (MvPowerSeries.ext fun d=>by simp [h d])
  let n := d.degree+1
  let p := MvPowerSeries.truncTotal n f
  have hn : n≠0 := Nat.succ_ne_zero _
  have hp : p≠0 := by
    intro h
    apply hd
    have hh := congrArg (fun polynomial : MvPolynomial σ K=>polynomial.coeff d) h
    change (MvPowerSeries.truncTotal n f).coeff d=0 at hh
    rw [MvPowerSeries.coeff_truncTotal f (show d.degree<n from Nat.lt_succ_self _)] at hh
    exact hh
  obtain ⟨a,ha⟩ : ∃ a : σ → K,eval a p≠0 := by
    by_contra h
    push Not at h
    apply hp
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using h x
  let q (i : σ) : MvPolynomial Unit K := C (a i)*X ()
  let g := eval₂ C q p
  have hgdeg : g.totalDegree<n :=
    (totalDegree_eval₂_linear p q (fun i=>by
      exact (totalDegree_mul _ _).trans (by simp))).trans_lt
      (MvPowerSeries.totalDegree_truncTotal_lt f hn)
  have hg : g≠0 := by
    intro h
    apply ha
    have hh := congrArg (eval (fun (_ : Unit)=>(1:K))) h
    have he : (eval (fun (_ : Unit)=>(1:K))).comp C = RingHom.id K := by
      ext c
      simp
    simpa [g,q,eval_eval₂,he] using hh
  refine ⟨a,?_⟩
  intro hz
  have hzconst : ∀ i : σ,(MvPowerSeries.C (a i)*
      MvPowerSeries.X () : MvPowerSeries Unit K).constantCoeff=0 := by
    intro i
    simp
  have he := MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
    (f:=f) (k:=n) hzconst
  rw [hz,map_zero] at he
  have hc : (g : MvPowerSeries Unit K) =
      MvPowerSeries.subst (fun i=>MvPowerSeries.C (a i)*MvPowerSeries.X ())
        (p : MvPowerSeries σ K) := by
    simpa only [q,MvPolynomial.coe_mul,MvPolynomial.coe_C,MvPolynomial.coe_X] using
      coe_eval₂_polynomials p q
  change 0 = MvPowerSeries.truncTotal n
    (MvPowerSeries.subst (fun i=>MvPowerSeries.C (a i)*MvPowerSeries.X ())
      (p : MvPowerSeries σ K)) at he
  rw [←hc,(MvPowerSeries.truncTotal_coe_eq_self_iff g hn).mpr hgdeg] at he
  exact hg he.symm

end
end PD4Tensor.Spreading

 

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ : Type*} [Field K] [Finite σ] [DecidableEq σ]

def linearChartVars (p : σ) (a : σ → K) (i : σ) : MvPowerSeries σ K :=
  if i=p then C (a i)*X p else X i+C (a i)*X p

 omit [Finite σ] in
 theorem linearChartVars_const (p : σ) (a : σ → K) (i : σ) :
    constantCoeff (linearChartVars p a i)=0 := by
  simp [linearChartVars]; split <;> simp

 theorem linearChartVars_hasSubst (p : σ) (a : σ → K) : HasSubst (linearChartVars p a) :=
  hasSubst_of_constantCoeff_zero (linearChartVars_const p a)

 theorem linearChartVars_comp (p : σ) (a b : σ → K)
    (hp : a p*b p=1) (hi : ∀ i,i≠p → b i+a i*b p=0) (i : σ) :
    subst (linearChartVars p b) (linearChartVars p a i)=X i := by
  have hb := linearChartVars_hasSubst p b
  by_cases h : i=p
  · subst i
    simp only [linearChartVars,ite_true,subst_mul hb,subst_C,subst_X hb]
    rw [←mul_assoc,←map_mul,hp,map_one,one_mul]
  · simp only [linearChartVars,h,ite_false,subst_add hb,subst_X hb,subst_mul hb,subst_C]
    calc
      X i+C (b i)*X p+C (a i)*(C (b p)*X p) = X i+C (b i+a i*b p)*X p := by
        rw [map_add,map_mul]; ring
      _ = X i := by rw [hi i h]; simp

def inverseChartPoint (p : σ) (a : σ → K) (i : σ) : K :=
  if i=p then (a p)⁻¹ else -(a i)/(a p)

 omit [Finite σ] in
 theorem chart_inverse_relations (p : σ) (a : σ → K) (hp : a p≠0) :
    a p*inverseChartPoint p a p=1 ∧
    (∀ i,i≠p → inverseChartPoint p a i+a i*inverseChartPoint p a p=0) ∧
    inverseChartPoint p a p*a p=1 ∧
    (∀ i,i≠p → a i+inverseChartPoint p a i*a p=0) := by
  refine ⟨by simp [inverseChartPoint,hp],?_,by simp [inverseChartPoint,hp],?_⟩
  · intro i hi
    simp [inverseChartPoint,hi,div_eq_mul_inv]
  · intro i hi
    simp [inverseChartPoint,hi,div_eq_mul_inv,hp]

def linearSeriesChart (p : σ) (a : σ → K) (hp : a p≠0) :
    MvPowerSeries σ K ≃ₐ[K] MvPowerSeries σ K := by
  let f : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K := substAlgHom (linearChartVars_hasSubst p a)
  let g : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K := substAlgHom (linearChartVars_hasSubst p (inverseChartPoint p a))
  have h := chart_inverse_relations p a hp
  have hfg : f.comp g=AlgHom.id K _ := by
    apply AlgHom.ext
    intro x
    simp only [f,g,AlgHom.comp_apply,substAlgHom_apply,AlgHom.id_apply]
    change subst (linearChartVars p a) (subst (linearChartVars p (inverseChartPoint p a)) x)=x
    rw [subst_comp_subst_apply (linearChartVars_hasSubst p _) (linearChartVars_hasSubst p _)]
    simp_rw [linearChartVars_comp p _ _ h.2.2.1 h.2.2.2]
    simp only [subst_self,Function.id_def]
  have hgf : g.comp f=AlgHom.id K _ := by
    apply AlgHom.ext
    intro x
    simp only [f,g,AlgHom.comp_apply,substAlgHom_apply,AlgHom.id_apply]
    change subst (linearChartVars p (inverseChartPoint p a)) (subst (linearChartVars p a) x)=x
    rw [subst_comp_subst_apply (linearChartVars_hasSubst p _) (linearChartVars_hasSubst p _)]
    simp_rw [linearChartVars_comp p _ _ h.1 h.2.1]
    simp only [subst_self,Function.id_def]
  exact AlgEquiv.ofAlgHom f g hfg hgf

 theorem linearSeriesChart_apply (p : σ) (a : σ → K) (hp : a p≠0)
    (f : MvPowerSeries σ K) : linearSeriesChart p a hp f=subst (linearChartVars p a) f := by
  simp [linearSeriesChart,AlgEquiv.ofAlgHom]

 def axisVars (p : σ) (i : σ) : MvPowerSeries Unit K := if i=p then X () else 0

 theorem axisVars_hasSubst (p : σ) : HasSubst (axisVars (K:=K) p) :=
    hasSubst_of_constantCoeff_zero fun i=>by simp [axisVars]; split <;> simp

 theorem axisVars_subst_linearChartVars (p : σ) (a : σ → K) (i : σ) :
    subst (axisVars p) (linearChartVars p a i)=C (a i)*X () := by
  have hh := axisVars_hasSubst (K:=K) p
  by_cases hi : i=p
  · subst i
    simp [linearChartVars,subst_mul hh,axisVars,subst_X hh]
  · simp [linearChartVars,hi,subst_add hh,subst_mul hh,subst_X hh,axisVars]

 

 theorem axis_linearSeriesChart (p : σ) (a : σ → K) (hp : a p≠0)
    (f : MvPowerSeries σ K) :
    subst (axisVars p) (linearSeriesChart p a hp f)=
      subst (fun i=>C (a i)*X ()) f := by
  rw [linearSeriesChart_apply,subst_comp_subst_apply (linearChartVars_hasSubst p a) (axisVars_hasSubst p)]
  simp_rw [axisVars_subst_linearChartVars]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ : Type*} [Field K] [Infinite K] [Finite σ] [DecidableEq σ]

 

theorem exists_regular_linear_chart (f : MvPowerSeries σ K)
    (hf : f≠0) (hf0 : constantCoeff f=0) :
    ∃ (p : σ) (a : σ → K) (hp : a p≠0),
      subst (axisVars (K:=K) p) (linearSeriesChart p a hp f)≠0 := by
  obtain ⟨a,ha⟩ := exists_nonzero_line f hf
  have hex : ∃ p,a p≠0 := by
    by_contra hn
    push Not at hn
    apply ha
    simp only [hn,map_zero,zero_mul]
    exact subst_zero_of_constantCoeff_zero hf0
  obtain ⟨p,hp⟩ := hex
  exact ⟨p,a,hp,by rwa [axis_linearSeriesChart]⟩

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K σ τ : Type*} [Field K] [Finite σ] [Finite τ]

 

theorem series_equiv_jet (E : MvPowerSeries σ K ≃+* MvPowerSeries τ K)
    {f : MvPowerSeries σ K} {n : ℕ} (hf : f∈(jetIdeal (K:=K) (σ:=σ))^n) :
    E f∈(jetIdeal (K:=K) (σ:=τ))^n := by
  have he : (jetIdeal (K:=K) (σ:=σ)).map E.toRingHom=jetIdeal (K:=K) (σ:=τ) := by
    rw [jetIdeal_eq_maximalIdeal,jetIdeal_eq_maximalIdeal]
    ext x
    change x∈(IsLocalRing.maximalIdeal (MvPowerSeries σ K)).map E ↔ _
    rw [←Ideal.symm_apply_mem_of_equiv_iff (f:=E)]
    simp only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,isUnit_map_iff E.symm]
  have h := Ideal.mem_map_of_mem E.toRingHom hf
  rwa [Ideal.map_pow,he] at h

variable [DecidableEq σ]

def polynomialChartVars (p : σ) (a : σ → K) (i : σ) : MvPolynomial σ K :=
  if i=p then MvPolynomial.C (a p)*MvPolynomial.X p
  else MvPolynomial.X i+MvPolynomial.C (a i)*MvPolynomial.X p

def polynomialChart (p : σ) (a : σ → K) : MvPolynomial σ K →+* MvPolynomial σ K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (polynomialChartVars p a)

 theorem polynomialChart_square (p : σ) (a : σ → K) (hp : a p≠0) :
    (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K)).comp (polynomialChart p a)=
      (linearSeriesChart p a hp).toRingHom.comp
        (algebraMap (MvPolynomial σ K) (MvPowerSeries σ K)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [polynomialChart,linearSeriesChart_apply,algebraMap_apply']
  · intro i
    simp only [RingHom.comp_apply,algebraMap_apply',MvPolynomial.coe_X]
    change ((polynomialChart p a (MvPolynomial.X i) : MvPolynomial σ K) : MvPowerSeries σ K)=
      linearSeriesChart p a hp (X i)
    rw [linearSeriesChart_apply,subst_X (linearChartVars_hasSubst p a)]
    by_cases hi : i=p <;> simp [polynomialChart,polynomialChartVars,linearChartVars,hi]

 theorem polynomialChart_injective (p : σ) (a : σ → K) (hp : a p≠0) :
    Function.Injective (polynomialChart p a) := by
  intro f g h
  apply MvPolynomial.coe_injective
  apply (linearSeriesChart p a hp).injective
  have hf := RingHom.congr_fun (polynomialChart_square p a hp) f
  have hg := RingHom.congr_fun (polynomialChart_square p a hp) g
  change (linearSeriesChart p a hp) (f : MvPowerSeries σ K)=
    (linearSeriesChart p a hp) (g : MvPowerSeries σ K)
  simp only [RingHom.comp_apply,algebraMap_apply'] at hf hg
  change ((polynomialChart p a f : MvPolynomial σ K) : MvPowerSeries σ K)=linearSeriesChart p a hp (f : MvPowerSeries σ K) at hf
  change ((polynomialChart p a g : MvPolynomial σ K) : MvPowerSeries σ K)=linearSeriesChart p a hp (g : MvPowerSeries σ K) at hg
  rw [←hf,←hg,h]

 theorem algebraic_linearSeriesChart (p : σ) (a : σ → K) (hp : a p≠0)
    {f : MvPowerSeries σ K} (hf : IsAlgebraic (MvPolynomial σ K) f) :
    IsAlgebraic (MvPolynomial σ K) (linearSeriesChart p a hp f) := by
  exact hf.ringHom_of_comp_eq (polynomialChart p a) (linearSeriesChart p a hp).toRingHom
    (polynomialChart_injective p a hp) (polynomialChart_square p a hp)

 theorem linearSeriesChart_symm_apply (p : σ) (a : σ → K) (hp : a p≠0)
    (f : MvPowerSeries σ K) :
    (linearSeriesChart p a hp).symm f=subst (linearChartVars p (inverseChartPoint p a)) f := by
  simp [linearSeriesChart,AlgEquiv.ofAlgHom]

 theorem algebraic_linearSeriesChart_symm (p : σ) (a : σ → K) (hp : a p≠0)
    {f : MvPowerSeries σ K} (hf : IsAlgebraic (MvPolynomial σ K) f) :
    IsAlgebraic (MvPolynomial σ K) ((linearSeriesChart p a hp).symm f) := by
  have hi : inverseChartPoint p a p≠0 := by simp [inverseChartPoint,hp]
  simpa only [linearSeriesChart_symm_apply,linearSeriesChart_apply] using
    algebraic_linearSeriesChart p (inverseChartPoint p a) hi hf

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries WithPiTopology
variable {K σ : Type*} [Field K] [Finite σ] [DecidableEq σ]

def axisEmbedding (p : σ) : Unit ↪ σ := ⟨fun _=>p,fun _ _ _=>Subsingleton.elim _ _⟩

theorem axis_subst_eq_killCompl (p : σ) (f : MvPowerSeries σ K) :
    subst (axisVars p) f=killCompl (axisEmbedding p) f := by
  let : UniformSpace K := ⊥
  let ε := killCompl (R:=K) (axisEmbedding p)
  have hε : Continuous ε := by
    apply continuous_pi
    intro d
    exact continuous_coeff K (Finsupp.embDomain (axisEmbedding p) d)
  have hvars : (fun i : σ=>ε (X i))=axisVars p := by
    funext i
    by_cases hi : i=p
    · subst i
      simp only [axisVars,ite_true]
      exact killCompl_X (R:=K) (e:=axisEmbedding p) ()
    · have hn : i∉Set.range (axisEmbedding p) := by
        rintro ⟨u,hu⟩
        exact hi hu.symm
      simpa [ε,axisVars,hi] using killCompl_X_eq_zero (R:=K) (e:=axisEmbedding p) hn
  have he := aeval_unique hε
  have hR := axisVars_hasSubst (K:=K) p
  change subst (axisVars p) f=ε f
  rw [←AlgHom.congr_fun he f]
  rw [←substAlgHom_apply hR,substAlgHom_eq_aeval hR]
  simp only [coe_aeval]
  change eval₂ (algebraMap K (MvPowerSeries Unit K)) (axisVars p) f=
    eval₂ (algebraMap K (MvPowerSeries Unit K)) (fun s=>ε (X s)) f
  rw [hvars]

 theorem option_axis_constant (f : MvPowerSeries (Option σ) K) :
    subst (axisVars none) f=(MvPowerSeries.optionEquivLeft σ K f).map
      (MvPowerSeries.constantCoeff : MvPowerSeries σ K →+* K) := by
  rw [axis_subst_eq_killCompl]
  apply PowerSeries.ext
  intro n
  change coeff (Finsupp.single () n) (killCompl (axisEmbedding none) f)=_
  rw [coeff_killCompl,PowerSeries.coeff_map,←coeff_zero_eq_constantCoeff_apply,
    coeff_coeff_optionEquivLeft]
  have he : Finsupp.embDomain (axisEmbedding (σ:=Option σ) none) (Finsupp.single () n)=
      Finsupp.optionElim n 0 := by
    rw [Finsupp.optionElim_zero,Finsupp.embDomain_single]
    rfl
  rw [he]

 theorem option_axis_rename (p : σ) (f : MvPowerSeries σ K) :
    subst (axisVars (K:=K) none) (rename (Equiv.optionSubtypeNe p).symm f)=subst (axisVars (K:=K) p) f := by
  rw [rename_eq_subst,subst_comp_subst_apply (HasSubst.X_comp _) (axisVars_hasSubst none)]
  congr 1
  funext i
  rw [Function.comp_apply,subst_X (axisVars_hasSubst none)]
  by_cases hi : i=p
  · subst i
    simp [axisVars]
  · simp [axisVars,hi,Equiv.optionSubtypeNe_symm_of_ne hi]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K τ : Type*} [Field K] [Finite τ]

 omit [Finite τ] in
 theorem residue_regular_of_constant_regular (f : PowerSeries (MvPowerSeries τ K))
    (hf : f.map (MvPowerSeries.constantCoeff : MvPowerSeries τ K →+* K)≠0) :
    f.map (IsLocalRing.residue (MvPowerSeries τ K))≠0 := by
  intro hz
  apply hf
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map,map_zero]
  have he := congrArg (PowerSeries.coeff n) hz
  rw [PowerSeries.coeff_map,map_zero] at he
  have hm : PowerSeries.coeff n f∈IsLocalRing.maximalIdeal (MvPowerSeries τ K) :=
    (IsLocalRing.residue_eq_zero_iff _).mp he
  rw [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff,isUnit_iff_ne_zero,not_not] at hm
  exact hm

end
end PD4Tensor.Spreading
end

end OAI
